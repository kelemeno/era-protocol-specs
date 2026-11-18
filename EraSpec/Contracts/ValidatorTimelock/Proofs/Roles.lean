import EraSpec.Contracts.ValidatorTimelock.Properties.Roles
import EraSpec.Contracts.ValidatorTimelock.Proofs.Model

/-!
# Proofs: the per-chain role registry and where the timelock forwards

On an empty registry every admin role is `DEFAULT_ADMIN_ROLE`, so the check of the first
grant, revoke, role-admin change or rotation on it is the chain-admin lookup
(`holdsAdminOf_of_empty`); a renounce cannot succeed there. `run_registry_trace` carries this
along runs, and the forwarding result adds that a forward needs a member.
-/

namespace Contracts.ValidatorTimelock

lemma chainAdmin_eq_some_iff {e : Env} {c a : Address} :
    chainAdmin e c = some a ↔
      ∃ id, e.chainIdOf c = some id ∧ e.zkChain id = c ∧ e.adminOf c = some a := by
  unfold chainAdmin
  cases h : e.chainIdOf c with
  | none => simp
  | some id =>
    by_cases h2 : e.zkChain id = c
    · simp [h2]
    · simp [h2]

lemma holdsAdminOf_of_empty {e : Env} {s : State} {c : Address} {r : Role} {x : Address}
    (hE : ChainRolesEmpty s c) (h : HoldsAdminOf e s c r x) : chainAdmin e c = some x := by
  unfold HoldsAdminOf at h
  have hd : getRoleAdmin s c r = DEFAULT_ADMIN_ROLE := by
    unfold getRoleAdmin
    split_ifs
    · rfl
    · exact hE.2 r
  rw [ite_eq_left hd] at h
  exact h

lemma registry_frame {k : Call} {s s' : State} {c : Address} (h : step k s = some s')
    (hw : ¬ k.action.writesRolesOf k.env c) :
    s'.members c = s.members c ∧ s'.adminRole c = s.adminRole c := by
  rw [step_post h]
  rcases k with ⟨e, x, a⟩
  cases a with
  | grantRole c₀ r a =>
    exact ⟨setMember_members_other (fun h' => hw h'.symm), rfl⟩
  | revokeRole c₀ r a =>
    exact ⟨setMember_members_other (fun h' => hw h'.symm), rfl⟩
  | renounceRole c₀ r =>
    exact ⟨setMember_members_other (fun h' => hw h'.symm), rfl⟩
  | setRoleAdmin c₀ r ar =>
    refine ⟨rfl, ?_⟩
    have hne : c ≠ c₀ := fun h' => hw h'.symm
    funext r'; simp [post, hne]
  | addValidatorRoles c₀ v p =>
    exact ⟨setMembers_members_other (fun h' => hw h'.symm), rfl⟩
  | removeValidatorRoles c₀ v p =>
    exact ⟨setMembers_members_other (fun h' => hw h'.symm), rfl⟩
  | addValidator c₀ v =>
    exact ⟨setMembers_members_other (fun h' => hw h'.symm), rfl⟩
  | removeValidator c₀ v =>
    exact ⟨setMembers_members_other (fun h' => hw h'.symm), rfl⟩
  | addValidatorForChainId id v =>
    exact ⟨setMembers_members_other (fun h' => hw h'.symm), rfl⟩
  | removeValidatorForChainId id v =>
    exact ⟨setMembers_members_other (fun h' => hw h'.symm), rfl⟩
  | _ => exact ⟨rfl, rfl⟩

lemma changeMany_from_empty {b : Bool} {e : Env} {x c v : Address} {rs : List Role}
    {s s' : State} (h : changeMany b e x c v rs s = some s') (hE : ChainRolesEmpty s c)
    (hne : ¬ ChainRolesEmpty s' c) : chainAdmin e c = some x := by
  cases rs with
  | nil =>
    simp only [changeMany, Option.some.injEq] at h
    subst h
    exact absurd hE hne
  | cons r rs => exact holdsAdminOf_of_empty hE (changeMany_head h).2

lemma step_registry_from_empty {k : Call} {s s' : State} {c : Address}
    (h : step k s = some s') (hE : ChainRolesEmpty s c) (hne : ¬ ChainRolesEmpty s' c) :
    k.action.writesRolesOf k.env c ∧ chainAdmin k.env c = some k.sender := by
  by_cases hw : k.action.writesRolesOf k.env c
  · refine ⟨hw, ?_⟩
    rcases k with ⟨e, x, a⟩
    cases a with
    | grantRole c₀ r a =>
      simp only [Action.writesRolesOf] at hw; subst hw
      exact holdsAdminOf_of_empty hE (changeRole_eq_some.mp h).2.1
    | revokeRole c₀ r a =>
      simp only [Action.writesRolesOf] at hw; subst hw
      exact holdsAdminOf_of_empty hE (changeRole_eq_some.mp h).2.1
    | renounceRole c₀ r =>
      simp only [Action.writesRolesOf] at hw; subst hw
      have hm := (renounceRole_eq_some.mp h).2.1
      rw [hE.1 r x] at hm
      exact absurd hm Bool.false_ne_true
    | setRoleAdmin c₀ r ar =>
      simp only [Action.writesRolesOf] at hw; subst hw
      exact holdsAdminOf_of_empty hE (setRoleAdmin_eq_some.mp h).2.1
    | addValidatorRoles c₀ v p =>
      simp only [Action.writesRolesOf] at hw; subst hw
      exact changeMany_from_empty h hE hne
    | removeValidatorRoles c₀ v p =>
      simp only [Action.writesRolesOf] at hw; subst hw
      exact changeMany_from_empty h hE hne
    | addValidator c₀ v =>
      simp only [Action.writesRolesOf] at hw; subst hw
      exact changeMany_from_empty h hE hne
    | removeValidator c₀ v =>
      simp only [Action.writesRolesOf] at hw; subst hw
      exact changeMany_from_empty h hE hne
    | addValidatorForChainId id v =>
      simp only [Action.writesRolesOf] at hw
      have h' : changeMany true e x (e.zkChain id) v addValidatorParams.roles s = some s' := h
      rw [hw] at h'
      exact changeMany_from_empty h' hE hne
    | removeValidatorForChainId id v =>
      simp only [Action.writesRolesOf] at hw
      have h' : changeMany false e x (e.zkChain id) v removeValidatorParams.roles s = some s' := h
      rw [hw] at h'
      exact changeMany_from_empty h' hE hne
    | _ => simp only [Action.writesRolesOf] at hw
  · exfalso
    apply hne
    obtain ⟨hm, ha⟩ := registry_frame h hw
    exact ⟨fun r a => by rw [hm]; exact hE.1 r a, fun r => by rw [ha]; exact hE.2 r⟩

lemma run_registry_trace {c : Address} :
    ∀ {s₀ s : State} {ks : List Call}, Run s₀ ks s → ChainRolesEmpty s₀ c →
      ¬ ChainRolesEmpty s c →
      ∃ k ∈ ks, k.action.writesRolesOf k.env c ∧ chainAdmin k.env c = some k.sender
  | _, _, _, .nil _, hE, hne => absurd hE hne
  | s₀, _, _, .cons (k := k) (s₁ := s₁) h1 h2, hE, hne => by
      by_cases hE₁ : ChainRolesEmpty s₁ c
      · obtain ⟨k', hk', hw, hadm⟩ := run_registry_trace h2 hE₁ hne
        exact ⟨k', List.mem_cons_of_mem _ hk', hw, hadm⟩
      · exact ⟨k, List.mem_cons_self, step_registry_from_empty h1 hE hE₁⟩

lemma init_rolesEmpty (c : Address) : ChainRolesEmpty init c :=
  ⟨fun _ _ => rfl, fun _ => rfl⟩

/-! ## The statements -/

theorem ForwardNeedsTheRole : Properties.ForwardNeedsTheRole := by
  rintro ⟨e, x, a⟩ s s' c r h hf
  cases a with
  | commitBatches c₀ lo hi =>
    simp only [Action.forward, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    obtain ⟨h1, _, h3, _⟩ := commitBatches_eq_some.mp h
    exact ⟨h1, h3⟩
  | revertBatches c₀ =>
    simp only [Action.forward, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    obtain ⟨h1, h2, _⟩ := (forwardOnly_eq_some reverter_ne).mp h
    exact ⟨h1, h2⟩
  | proveBatches c₀ =>
    simp only [Action.forward, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    obtain ⟨h1, h2, _⟩ := (forwardOnly_eq_some prover_ne).mp h
    exact ⟨h1, h2⟩
  | executeBatches c₀ lo hi =>
    simp only [Action.forward, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    obtain ⟨h1, _, _, h4, _⟩ := executeBatches_eq_some.mp h
    exact ⟨h1, h4⟩
  | upgradeChainFromVersion c₀ w =>
    simp only [Action.forward, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    obtain ⟨h1, h2, _⟩ := (forwardOnly_eq_some upgrader_ne).mp h
    exact ⟨h1, h2⟩
  | _ => simp only [Action.forward, reduceCtorEq] at hf

theorem RegistryWriters : Properties.RegistryWriters := by
  intro k s s' c h hne
  by_contra hw
  obtain ⟨hm, ha⟩ := registry_frame h hw
  rcases hne with hne | hne
  · exact hne hm
  · exact hne ha

theorem RolesTraceToAVerifiedChainAdmin : Properties.RolesTraceToAVerifiedChainAdmin :=
  ⟨init_rolesEmpty, fun _ _ _ _ hE h hne => run_registry_trace h hE hne⟩

theorem ForwardsOnlyToOnceRegisteredChains : Properties.ForwardsOnlyToOnceRegisteredChains := by
  intro ks s s' k c r hrun hstep hf
  obtain ⟨hmem, -⟩ := ForwardNeedsTheRole k s s' c r hstep hf
  have hne : ¬ ChainRolesEmpty s c := fun hE => by
    rw [hE.1 r k.sender] at hmem
    exact Bool.false_ne_true hmem
  obtain ⟨k₀, hk₀, hw, hadm⟩ := run_registry_trace hrun (init_rolesEmpty c) hne
  exact ⟨k₀, hk₀, hw, chainAdmin_eq_some_iff.mp hadm⟩

/-! ## The countermodel and the witness -/

lemma map_of_eq_some {β : Type} {o : Option State} {s : State} (h : o = some s) (f : State → β)
    {b : β} (hb : o.map f = some b) : f s = b := by
  rw [h] at hb; simpa using hb

theorem UncheckedLookupGrantsOnUnregisteredChain :
    Properties.UncheckedLookupGrantsOnUnregisteredChain := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp
      (show (grantRoleUnchecked (vtEnv 0) vtFakeAdmin vtFake COMMITTER_ROLE vtFakeAdmin
        init).isSome = true by decide)
    have hstep : step (vtCall 0 vtFakeAdmin (.commitBatches vtFake 1 1)) s =
        (grantRoleUnchecked (vtEnv 0) vtFakeAdmin vtFake COMMITTER_ROLE vtFakeAdmin init).bind
          (step (vtCall 0 vtFakeAdmin (.commitBatches vtFake 1 1))) := by
      rw [hs]; rfl
    obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp
      (show (step (vtCall 0 vtFakeAdmin (.commitBatches vtFake 1 1)) s).isSome = true by
        rw [hstep]; decide)
    exact ⟨s, s', hs, map_of_eq_some hs (fun s => s.members vtFake COMMITTER_ROLE vtFakeAdmin)
      (by decide), hs'⟩
  · apply step_none_of_exec
    decide

theorem RoleDelegationWitness : Properties.RoleDelegationWitness := by
  obtain ⟨s₀, h0, e0⟩ := exists_run_of_isSome (ks := vtSetupCalls) (s := init) (by decide)
  obtain ⟨s, h1, e1⟩ := exists_run_of_isSome (s := s₀)
    (ks := [vtCall 1 vtAdmin (.setRoleAdmin vtChain COMMITTER_ROLE OPTIONAL_COMMITTER_ADMIN_ROLE),
            vtCall 1 vtAdmin (.grantRole vtChain OPTIONAL_COMMITTER_ADMIN_ROLE vtManager),
            vtCall 2 vtManager (.grantRole vtChain COMMITTER_ROLE vtDelegate)])
    (by rw [← exec_split e0]; decide)
  have e01 := exec_snoc_of e0 e1
  obtain ⟨s', _, e2⟩ := exists_run_of_isSome (s := s)
    (ks := [vtCall 3 vtDelegate (.commitBatches vtChain 1 1)])
    (by rw [← exec_split e01]; decide)
  refine ⟨s₀, s, s', h0, h1, by decide, by decide,
    map_of_exec e01 (fun s => s.members vtChain COMMITTER_ROLE vtDelegate) (by decide),
    step_of_exec e2, ?_⟩
  apply step_none_of_exec
  rw [← exec_split e01]
  decide

end Contracts.ValidatorTimelock
