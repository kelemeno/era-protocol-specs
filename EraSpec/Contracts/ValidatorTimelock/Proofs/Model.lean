import EraSpec.Contracts.ValidatorTimelock.Properties.Model

/-!
# Proofs: what each `ValidatorTimelock` entry point checks and writes

Each entry point's definition is a chain of `if … then none`; `ite_none_eq_some` peels one
test at a time. The role constants are nonzero by evaluation, so `hasRole` on them is the
membership bit (`hasRole_of_ne`). The lemmas here are shared by the run-level proofs
(`Proofs.Delay`, `Proofs.Roles`, `Proofs.Ownership`).
-/

namespace Contracts.ValidatorTimelock

/-! ## Basic lemmas -/

@[simp] lemma upd_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) :
    upd f a b a = b := by simp [upd]

lemma upd_other {α β : Type} [DecidableEq α] (f : α → β) {a x : α} (b : β) (h : x ≠ a) :
    upd f a b x = f x := by simp [upd, h]

lemma ite_none_eq_some {α : Type} {p : Prop} [Decidable p] {o : Option α} {a : α} :
    (if p then none else o) = some a ↔ ¬ p ∧ o = some a := by
  split_ifs with h <;> simp [h]

lemma some_eq_some_iff' {α : Type} {a b : α} : some a = some b ↔ b = a := by
  simp [eq_comm]

lemma committer_ne : COMMITTER_ROLE ≠ DEFAULT_ADMIN_ROLE := by decide
lemma reverter_ne : REVERTER_ROLE ≠ DEFAULT_ADMIN_ROLE := by decide
lemma prover_ne : PROVER_ROLE ≠ DEFAULT_ADMIN_ROLE := by decide
lemma executor_ne : EXECUTOR_ROLE ≠ DEFAULT_ADMIN_ROLE := by decide
lemma upgrader_ne : UPGRADER_ROLE ≠ DEFAULT_ADMIN_ROLE := by decide
lemma precommitter_ne : PRECOMMITTER_ROLE ≠ DEFAULT_ADMIN_ROLE := by decide

lemma hasRole_of_ne {e : Env} {s : State} {c : Address} {r : Role} {a : Address}
    (h : r ≠ DEFAULT_ADMIN_ROLE) : hasRole e s c r a = some (s.members c r a) := by
  simp [hasRole, h]

lemma hasRole_default_iff {e : Env} {s : State} {c a : Address} :
    hasRole e s c DEFAULT_ADMIN_ROLE a = some true ↔ chainAdmin e c = some a := by
  unfold hasRole
  simp only [ite_true]
  cases chainAdmin e c with
  | none => simp
  | some adm => simp [eq_comm]

lemma hasRole_true_iff {e : Env} {s : State} {c : Address} {r : Role} {a : Address} :
    hasRole e s c r a = some true ↔
      (if r = DEFAULT_ADMIN_ROLE then chainAdmin e c = some a else s.members c r a = true) := by
  by_cases h : r = DEFAULT_ADMIN_ROLE
  · subst h; rw [hasRole_default_iff]; simp
  · rw [hasRole_of_ne h]; simp [h]

lemma holdsAdminOf_iff {e : Env} {s : State} {c : Address} {r : Role} {x : Address} :
    hasRole e s c (getRoleAdmin s c r) x = some true ↔ HoldsAdminOf e s c r x := by
  rw [hasRole_true_iff]; rfl

lemma not_ne_some {α : Type} {o : Option α} {a : α} : ¬ (o ≠ some a) ↔ o = some a := not_not

/-! ## Success of each entry point -/

lemma initializeTimelock_eq_some {o : Address} {d : ℕ} {s s' : State} :
    initializeTimelock o d s = some s' ↔
      s.initialized = false ∧ d ≤ MAX_EXECUTION_DELAY ∧
        s' = { s with initialized := true, owner := o, pendingOwner := 0, executionDelay := d } := by
  unfold initializeTimelock
  simp only [ite_none_eq_some, some_eq_some_iff', not_lt, Bool.not_eq_true]

lemma transferOwnership_eq_some {x n : Address} {s s' : State} :
    transferOwnership x n s = some s' ↔ x = s.owner ∧ s' = { s with pendingOwner := n } := by
  unfold transferOwnership
  simp only [ite_none_eq_some, some_eq_some_iff', not_not]

lemma acceptOwnership_eq_some {x : Address} {s s' : State} :
    acceptOwnership x s = some s' ↔
      x = s.pendingOwner ∧ s' = { s with owner := x, pendingOwner := 0 } := by
  unfold acceptOwnership
  simp only [ite_none_eq_some, some_eq_some_iff', not_not]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2⟩

lemma renounceOwnership_eq_some {x : Address} {s s' : State} :
    renounceOwnership x s = some s' ↔ x = s.owner ∧ s' = { s with owner := 0, pendingOwner := 0 } := by
  unfold renounceOwnership
  simp only [ite_none_eq_some, some_eq_some_iff', not_not]

lemma setExecutionDelay_eq_some {x : Address} {d : ℕ} {s s' : State} :
    setExecutionDelay x d s = some s' ↔
      x = s.owner ∧ d ≤ MAX_EXECUTION_DELAY ∧ s' = { s with executionDelay := d } := by
  unfold setExecutionDelay
  simp only [ite_none_eq_some, some_eq_some_iff', not_not, not_lt]

lemma setChainExecutionDelay_eq_some {x c : Address} {d : ℕ} {s s' : State} :
    setChainExecutionDelay x c d s = some s' ↔
      x = s.owner ∧ d ≤ MAX_EXECUTION_DELAY ∧ s' = { s with chainDelay := upd s.chainDelay c d } := by
  unfold setChainExecutionDelay
  simp only [ite_none_eq_some, some_eq_some_iff', not_not, not_lt]

lemma increaseChainExecutionDelay_eq_some {e : Env} {x c : Address} {d : ℕ} {s s' : State} :
    increaseChainExecutionDelay e x c d s = some s' ↔
      chainAdmin e c = some x ∧ d ≤ MAX_EXECUTION_DELAY ∧ enforcedDelay s c < d ∧
        s' = { s with chainDelay := upd s.chainDelay c d } := by
  unfold increaseChainExecutionDelay
  simp only [ite_none_eq_some, some_eq_some_iff', not_ne_some, not_lt, not_le,
    hasRole_default_iff]

lemma changeRole_eq_some {b : Bool} {e : Env} {x c : Address} {r : Role} {a : Address}
    {s s' : State} :
    changeRole b e x c r a s = some s' ↔
      r ≠ DEFAULT_ADMIN_ROLE ∧ HoldsAdminOf e s c r x ∧ s' = setMember s c r a b := by
  unfold changeRole
  simp only [ite_none_eq_some, some_eq_some_iff', not_ne_some, holdsAdminOf_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3⟩

lemma renounceRole_eq_some {e : Env} {x c : Address} {r : Role} {s s' : State} :
    renounceRole e x c r s = some s' ↔
      r ≠ DEFAULT_ADMIN_ROLE ∧ s.members c r x = true ∧ s' = setMember s c r x false := by
  unfold renounceRole
  simp only [ite_none_eq_some, some_eq_some_iff', not_ne_some]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [hasRole_of_ne h2] at h1
    exact ⟨h2, Option.some.inj h1, h3⟩
  · rintro ⟨h1, h2, h3⟩
    rw [hasRole_of_ne h1, h2]
    exact ⟨rfl, h1, h3⟩

lemma setRoleAdmin_eq_some {e : Env} {x c : Address} {r ar : Role} {s s' : State} :
    setRoleAdmin e x c r ar s = some s' ↔
      r ≠ DEFAULT_ADMIN_ROLE ∧ HoldsAdminOf e s c r x ∧
        s' = { s with adminRole := fun c' r' => if c' = c ∧ r' = r then ar else s.adminRole c' r' } := by
  unfold setRoleAdmin
  simp only [ite_none_eq_some, some_eq_some_iff', not_ne_some, holdsAdminOf_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3⟩

lemma commitBatches_eq_some {e : Env} {x c : Address} {lo hi : ℕ} {s s' : State} :
    commitBatches e x c lo hi s = some s' ↔
      s.members c COMMITTER_ROLE x = true ∧ validRange lo hi ∧ e.forwardOk = true ∧
        s' = recordCommit s c lo hi e.now := by
  unfold commitBatches
  rw [hasRole_of_ne committer_ne]
  by_cases h1 : s.members c COMMITTER_ROLE x = true <;> by_cases h2 : validRange lo hi <;>
    by_cases h3 : e.forwardOk = true <;> simp [h1, h2, h3, eq_comm]

lemma executeBatches_eq_some {e : Env} {x c : Address} {lo hi : ℕ} {s s' : State} :
    executeBatches e x c lo hi s = some s' ↔
      s.members c EXECUTOR_ROLE x = true ∧ validRange lo hi ∧ delayPassed s c lo hi e.now ∧
        e.forwardOk = true ∧ s' = s := by
  unfold executeBatches
  rw [hasRole_of_ne executor_ne]
  by_cases h1 : s.members c EXECUTOR_ROLE x = true <;> by_cases h2 : validRange lo hi <;>
    by_cases h3 : delayPassed s c lo hi e.now <;> by_cases h4 : e.forwardOk = true <;>
    simp [h1, h2, h3, h4, eq_comm]

lemma forwardOnly_eq_some {e : Env} {x c : Address} {r : Role} {s s' : State}
    (hr : r ≠ DEFAULT_ADMIN_ROLE) :
    forwardOnly e x c r s = some s' ↔ s.members c r x = true ∧ e.forwardOk = true ∧ s' = s := by
  unfold forwardOnly
  rw [hasRole_of_ne hr]
  by_cases h1 : s.members c r x = true <;> by_cases h2 : e.forwardOk = true <;>
    simp [h1, h2, eq_comm]

/-! ## The rotation wrappers -/

lemma setMembers_nil (s : State) (c v : Address) (b : Bool) : setMembers s c v [] b = s := by
  ext <;> simp [setMembers]

lemma setMembers_cons (s : State) (c v : Address) (r : Role) (rs : List Role) (b : Bool) :
    setMembers (setMember s c r v b) c v rs b = setMembers s c v (r :: rs) b := by
  ext c' r' a'
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp only [setMembers, setMember, List.mem_cons]
    by_cases h1 : c' = c <;> by_cases h2 : r' ∈ rs <;> by_cases h3 : a' = v <;>
      by_cases h4 : r' = r <;> simp [h1, h2, h3, h4]
  · rfl
  · rfl

lemma changeMany_eq_some {b : Bool} {e : Env} {x c v : Address} :
    ∀ {rs : List Role} {s s' : State}, changeMany b e x c v rs s = some s' →
      s' = setMembers s c v rs b
  | [], s, s', h => by
      simp only [changeMany, Option.some.injEq] at h
      rw [← h, setMembers_nil]
  | r :: rs, s, s', h => by
      simp only [changeMany] at h
      cases h1 : changeRole b e x c r v s with
      | none => rw [h1] at h; simp at h
      | some s₁ =>
        rw [h1] at h
        have h2 := changeMany_eq_some (rs := rs) h
        obtain ⟨_, _, hs₁⟩ := changeRole_eq_some.mp h1
        rw [h2, hs₁, setMembers_cons]

/-- The first grant or revoke of a non-empty successful rotation passed its check on the
starting state. -/
lemma changeMany_head {b : Bool} {e : Env} {x c v : Address} {r : Role} {rs : List Role}
    {s s' : State} (h : changeMany b e x c v (r :: rs) s = some s') :
    r ≠ DEFAULT_ADMIN_ROLE ∧ HoldsAdminOf e s c r x := by
  simp only [changeMany] at h
  cases h1 : changeRole b e x c r v s with
  | none => rw [h1] at h; simp at h
  | some s₁ =>
    obtain ⟨h2, h3, _⟩ := changeRole_eq_some.mp h1
    exact ⟨h2, h3⟩

/-! ## Field lemmas -/

lemma setMember_members_other {s : State} {c c' : Address} {r : Role} {a : Address} {b : Bool}
    (h : c' ≠ c) : (setMember s c r a b).members c' = s.members c' := by
  funext r' a'; simp [setMember, h]

lemma setMembers_members_other {s : State} {c c' v : Address} {rs : List Role} {b : Bool}
    (h : c' ≠ c) : (setMembers s c v rs b).members c' = s.members c' := by
  funext r' a'; simp [setMembers, h]

lemma recordCommit_other {s : State} {c c' : Address} {lo hi now : ℕ} (h : c' ≠ c) :
    (recordCommit s c lo hi now).committedAt c' = s.committedAt c' := by
  funext i; simp [recordCommit, h]

lemma upd_fun_other {β : Type} {f : Address → β} {c c' : Address} {b : β} (h : c' ≠ c) :
    upd f c b c' = f c' := upd_other f b h

/-! ## The post-state of a successful call -/

/-- What a successful call leaves, by entry point (`step_post`). -/
def post (k : Call) (s : State) : State :=
  match k.action with
  | .initializeTimelock o d =>
      { s with initialized := true, owner := o, pendingOwner := 0, executionDelay := d }
  | .transferOwnership n => { s with pendingOwner := n }
  | .acceptOwnership => { s with owner := k.sender, pendingOwner := 0 }
  | .renounceOwnership => { s with owner := 0, pendingOwner := 0 }
  | .setExecutionDelay d => { s with executionDelay := d }
  | .increaseChainExecutionDelay c d => { s with chainDelay := upd s.chainDelay c d }
  | .setChainExecutionDelay c d => { s with chainDelay := upd s.chainDelay c d }
  | .grantRole c r a => setMember s c r a true
  | .revokeRole c r a => setMember s c r a false
  | .renounceRole c r => setMember s c r k.sender false
  | .setRoleAdmin c r ar =>
      { s with adminRole := fun c' r' => if c' = c ∧ r' = r then ar else s.adminRole c' r' }
  | .addValidatorRoles c v p => setMembers s c v p.roles true
  | .removeValidatorRoles c v p => setMembers s c v p.roles false
  | .addValidator c v => setMembers s c v addValidatorParams.roles true
  | .removeValidator c v => setMembers s c v removeValidatorParams.roles false
  | .addValidatorForChainId id v => setMembers s (k.env.zkChain id) v addValidatorParams.roles true
  | .removeValidatorForChainId id v =>
      setMembers s (k.env.zkChain id) v removeValidatorParams.roles false
  | .commitBatches c lo hi => recordCommit s c lo hi k.env.now
  | .revertBatches _ | .proveBatches _ | .executeBatches _ _ _ | .upgradeChainFromVersion _ _ => s

lemma step_post {k : Call} {s s' : State} (h : step k s = some s') : s' = post k s := by
  rcases k with ⟨e, x, a⟩
  cases a with
  | initializeTimelock o d => exact (initializeTimelock_eq_some.mp h).2.2
  | transferOwnership n => exact (transferOwnership_eq_some.mp h).2
  | acceptOwnership => exact (acceptOwnership_eq_some.mp h).2
  | renounceOwnership => exact (renounceOwnership_eq_some.mp h).2
  | setExecutionDelay d => exact (setExecutionDelay_eq_some.mp h).2.2
  | increaseChainExecutionDelay c d => exact (increaseChainExecutionDelay_eq_some.mp h).2.2.2
  | setChainExecutionDelay c d => exact (setChainExecutionDelay_eq_some.mp h).2.2
  | grantRole c r a => exact (changeRole_eq_some.mp h).2.2
  | revokeRole c r a => exact (changeRole_eq_some.mp h).2.2
  | renounceRole c r => exact (renounceRole_eq_some.mp h).2.2
  | setRoleAdmin c r ar => exact (setRoleAdmin_eq_some.mp h).2.2
  | addValidatorRoles c v p => exact changeMany_eq_some h
  | removeValidatorRoles c v p => exact changeMany_eq_some h
  | addValidator c v => exact changeMany_eq_some h
  | removeValidator c v => exact changeMany_eq_some h
  | addValidatorForChainId id v => exact changeMany_eq_some h
  | removeValidatorForChainId id v => exact changeMany_eq_some h
  | commitBatches c lo hi => exact (commitBatches_eq_some.mp h).2.2.2
  | revertBatches c => exact ((forwardOnly_eq_some reverter_ne).mp h).2.2
  | proveBatches c => exact ((forwardOnly_eq_some prover_ne).mp h).2.2
  | executeBatches c lo hi => exact (executeBatches_eq_some.mp h).2.2.2.2
  | upgradeChainFromVersion c w => exact ((forwardOnly_eq_some upgrader_ne).mp h).2.2

lemma step_eq_of_action {k : Call} {a : Action} (h : k.action = a) (s : State) :
    step k s = step ⟨k.env, k.sender, a⟩ s := by
  rcases k with ⟨e, x, a'⟩; simp only at h; subst h; rfl

lemma post_committedAt_of_not_commits {k : Call} {s : State} {c : Address} {i : ℕ}
    (h : ¬ k.action.commits c i) : (post k s).committedAt c i = s.committedAt c i := by
  rcases k with ⟨e, x, a⟩
  cases a with
  | commitBatches c' lo hi =>
    simp only [Action.commits] at h
    simp only [post, recordCommit]
    exact ite_eq_right h
  | _ => rfl

lemma post_committedAt_of_commits {k : Call} {s : State} {c : Address} {i : ℕ}
    (h : k.action.commits c i) : (post k s).committedAt c i = k.env.now % UINT32 := by
  rcases k with ⟨e, x, a⟩
  cases a with
  | commitBatches c' lo hi =>
    simp only [Action.commits] at h
    simp only [post, recordCommit]
    exact ite_eq_left h
  | _ => simp only [Action.commits] at h

lemma post_delays_of_not_writer {k : Call} {s : State}
    (h1 : ∀ o d, k.action ≠ .initializeTimelock o d) (h2 : ∀ d, k.action ≠ .setExecutionDelay d)
    (h3 : ∀ c d, k.action ≠ .setChainExecutionDelay c d)
    (h4 : ∀ c d, k.action ≠ .increaseChainExecutionDelay c d) :
    (post k s).executionDelay = s.executionDelay ∧ (post k s).chainDelay = s.chainDelay := by
  rcases k with ⟨e, x, a⟩
  cases a with
  | initializeTimelock o d => exact absurd rfl (h1 o d)
  | setExecutionDelay d => exact absurd rfl (h2 d)
  | setChainExecutionDelay c d => exact absurd rfl (h3 c d)
  | increaseChainExecutionDelay c d => exact absurd rfl (h4 c d)
  | _ => exact ⟨rfl, rfl⟩

lemma run_committedAt_frame {c : Address} {i : ℕ} :
    ∀ {s s' : State} {ks : List Call}, Run s ks s' → (∀ k ∈ ks, ¬ k.action.commits c i) →
      s'.committedAt c i = s.committedAt c i
  | _, _, _, .nil _, _ => rfl
  | _, _, _, .cons (k := k) h1 h2, hno => by
      rw [run_committedAt_frame h2 (fun k' hk' => hno k' (List.mem_cons_of_mem _ hk')),
        step_post h1, post_committedAt_of_not_commits (hno k List.mem_cons_self)]

lemma enforcedDelay_eq_max (s : State) (c : Address) :
    enforcedDelay s c = max (s.chainDelay c) s.executionDelay := by
  unfold enforcedDelay
  split_ifs with h
  · exact (max_eq_left (le_of_lt h)).symm
  · exact (max_eq_right (not_lt.mp h)).symm

/-! ## The statements -/

theorem ForwardingGuardsExact : Properties.ForwardingGuardsExact := by
  intro e x c s s'
  refine ⟨fun lo hi => commitBatches_eq_some, fun lo hi => executeBatches_eq_some,
    forwardOnly_eq_some reverter_ne, forwardOnly_eq_some prover_ne,
    fun _ => forwardOnly_eq_some upgrader_ne⟩

theorem DelaySettersExact : Properties.DelaySettersExact := by
  intro e x c d s s'
  exact ⟨setExecutionDelay_eq_some, setChainExecutionDelay_eq_some,
    increaseChainExecutionDelay_eq_some⟩

theorem RegistryWritesExact : Properties.RegistryWritesExact := by
  intro e x c r ar a s s'
  exact ⟨changeRole_eq_some, changeRole_eq_some, renounceRole_eq_some, setRoleAdmin_eq_some⟩

theorem OwnerCallsExact : Properties.OwnerCallsExact := by
  intro e x o n d s s'
  exact ⟨initializeTimelock_eq_some, transferOwnership_eq_some, acceptOwnership_eq_some,
    renounceOwnership_eq_some⟩

theorem DefaultAdminRoleIsNotTransferable : Properties.DefaultAdminRoleIsNotTransferable := by
  intro e x c a ar s
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [Option.eq_none_iff_forall_ne_some] <;> intro s' h
  · exact (changeRole_eq_some.mp h).1 rfl
  · exact (changeRole_eq_some.mp h).1 rfl
  · exact (renounceRole_eq_some.mp h).1 rfl
  · exact (setRoleAdmin_eq_some.mp h).1 rfl

theorem RotationIsItsGrants : Properties.RotationIsItsGrants := by
  refine ⟨rfl, rfl, ?_⟩
  intro e x c v id p s s'
  exact ⟨changeMany_eq_some, changeMany_eq_some, changeMany_eq_some, changeMany_eq_some,
    changeMany_eq_some, changeMany_eq_some⟩

theorem CallsTouchOnlyTheirChain : Properties.CallsTouchOnlyTheirChain := by
  rintro ⟨e, x, a⟩ s s' c h hc
  cases a with
  | initializeTimelock o d =>
    obtain ⟨_, _, rfl⟩ := initializeTimelock_eq_some.mp h; exact ⟨rfl, rfl, rfl, rfl⟩
  | transferOwnership n =>
    obtain ⟨_, rfl⟩ := transferOwnership_eq_some.mp h; exact ⟨rfl, rfl, rfl, rfl⟩
  | acceptOwnership =>
    obtain ⟨_, rfl⟩ := acceptOwnership_eq_some.mp h; exact ⟨rfl, rfl, rfl, rfl⟩
  | renounceOwnership =>
    obtain ⟨_, rfl⟩ := renounceOwnership_eq_some.mp h; exact ⟨rfl, rfl, rfl, rfl⟩
  | setExecutionDelay d =>
    obtain ⟨_, _, rfl⟩ := setExecutionDelay_eq_some.mp h; exact ⟨rfl, rfl, rfl, rfl⟩
  | increaseChainExecutionDelay c₀ d =>
    have hne : c ≠ c₀ := fun h' => hc (by simp [Action.chain, h'])
    obtain ⟨_, _, _, rfl⟩ := increaseChainExecutionDelay_eq_some.mp h
    exact ⟨rfl, rfl, upd_fun_other hne, rfl⟩
  | setChainExecutionDelay c₀ d =>
    have hne : c ≠ c₀ := fun h' => hc (by simp [Action.chain, h'])
    obtain ⟨_, _, rfl⟩ := setChainExecutionDelay_eq_some.mp h
    exact ⟨rfl, rfl, upd_fun_other hne, rfl⟩
  | grantRole c₀ r a =>
    have hne : c ≠ c₀ := fun h' => hc (by simp [Action.chain, h'])
    obtain ⟨_, _, rfl⟩ := changeRole_eq_some.mp h
    exact ⟨setMember_members_other hne, rfl, rfl, rfl⟩
  | revokeRole c₀ r a =>
    have hne : c ≠ c₀ := fun h' => hc (by simp [Action.chain, h'])
    obtain ⟨_, _, rfl⟩ := changeRole_eq_some.mp h
    exact ⟨setMember_members_other hne, rfl, rfl, rfl⟩
  | renounceRole c₀ r =>
    have hne : c ≠ c₀ := fun h' => hc (by simp [Action.chain, h'])
    obtain ⟨_, _, rfl⟩ := renounceRole_eq_some.mp h
    exact ⟨setMember_members_other hne, rfl, rfl, rfl⟩
  | setRoleAdmin c₀ r ar =>
    have hne : c ≠ c₀ := fun h' => hc (by simp [Action.chain, h'])
    obtain ⟨_, _, rfl⟩ := setRoleAdmin_eq_some.mp h
    refine ⟨rfl, ?_, rfl, rfl⟩
    funext r'; simp [hne]
  | addValidatorRoles c₀ v p =>
    have hne : c ≠ c₀ := fun h' => hc (by simp [Action.chain, h'])
    rw [changeMany_eq_some h]; exact ⟨setMembers_members_other hne, rfl, rfl, rfl⟩
  | removeValidatorRoles c₀ v p =>
    have hne : c ≠ c₀ := fun h' => hc (by simp [Action.chain, h'])
    rw [changeMany_eq_some h]; exact ⟨setMembers_members_other hne, rfl, rfl, rfl⟩
  | addValidator c₀ v =>
    have hne : c ≠ c₀ := fun h' => hc (by simp [Action.chain, h'])
    rw [changeMany_eq_some h]; exact ⟨setMembers_members_other hne, rfl, rfl, rfl⟩
  | removeValidator c₀ v =>
    have hne : c ≠ c₀ := fun h' => hc (by simp [Action.chain, h'])
    rw [changeMany_eq_some h]; exact ⟨setMembers_members_other hne, rfl, rfl, rfl⟩
  | addValidatorForChainId id v =>
    have hne : c ≠ e.zkChain id := fun h' => hc (by simp [Action.chain, h'])
    rw [changeMany_eq_some h]; exact ⟨setMembers_members_other hne, rfl, rfl, rfl⟩
  | removeValidatorForChainId id v =>
    have hne : c ≠ e.zkChain id := fun h' => hc (by simp [Action.chain, h'])
    rw [changeMany_eq_some h]; exact ⟨setMembers_members_other hne, rfl, rfl, rfl⟩
  | commitBatches c₀ lo hi =>
    have hne : c ≠ c₀ := fun h' => hc (by simp [Action.chain, h'])
    obtain ⟨_, _, _, rfl⟩ := commitBatches_eq_some.mp h
    exact ⟨rfl, rfl, rfl, recordCommit_other hne⟩
  | revertBatches c₀ =>
    obtain ⟨_, _, rfl⟩ := (forwardOnly_eq_some reverter_ne).mp h; exact ⟨rfl, rfl, rfl, rfl⟩
  | proveBatches c₀ =>
    obtain ⟨_, _, rfl⟩ := (forwardOnly_eq_some prover_ne).mp h; exact ⟨rfl, rfl, rfl, rfl⟩
  | executeBatches c₀ lo hi =>
    obtain ⟨_, _, _, _, rfl⟩ := executeBatches_eq_some.mp h; exact ⟨rfl, rfl, rfl, rfl⟩
  | upgradeChainFromVersion c₀ w =>
    obtain ⟨_, _, rfl⟩ := (forwardOnly_eq_some upgrader_ne).mp h; exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Runs and evaluation -/

lemma exec_eq_some_iff : ∀ {ks : List Call} {s s' : State}, exec ks s = some s' ↔ Run s ks s'
  | [], s, s' => by
      constructor
      · intro h; simp only [exec, Option.some.injEq] at h; subst h; exact Run.nil _
      · intro h; cases h; rfl
  | k :: ks, s, s' => by
      constructor
      · intro h
        simp only [exec] at h
        cases h1 : step k s with
        | none => rw [h1] at h; simp at h
        | some s₁ => rw [h1] at h; exact Run.cons h1 (exec_eq_some_iff.mp h)
      · intro h
        cases h with
        | cons h1 h2 => simp only [exec, h1, Option.bind_some]; exact exec_eq_some_iff.mpr h2

lemma exec_append : ∀ (ks ks' : List Call) (s : State),
    exec (ks ++ ks') s = (exec ks s).bind (exec ks')
  | [], ks', s => by simp [exec]
  | k :: ks, ks', s => by
      simp only [List.cons_append, exec]
      cases step k s with
      | none => rfl
      | some s₁ => simp only [Option.bind_some]; exact exec_append ks ks' s₁

lemma run_append {s s₁ s₂ : State} {ks ks' : List Call} (h1 : Run s ks s₁) (h2 : Run s₁ ks' s₂) :
    Run s (ks ++ ks') s₂ := by
  rw [← exec_eq_some_iff] at h1 h2 ⊢
  rw [exec_append, h1, Option.bind_some, h2]

/-- A run whose evaluation is `some`: for the witnesses, which compute with `decide`. -/
lemma exists_run_of_isSome {ks : List Call} {s : State} (h : (exec ks s).isSome = true) :
    ∃ s', Run s ks s' ∧ exec ks s = some s' := by
  obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp h
  exact ⟨s', exec_eq_some_iff.mp hs', hs'⟩

lemma map_of_exec {β : Type} {ks : List Call} {s s' : State} (h : exec ks s = some s')
    (f : State → β) {b : β} (hb : (exec ks s).map f = some b) : f s' = b := by
  rw [h] at hb; simpa using hb

lemma exec_split {ks ks' : List Call} {s s₁ : State} (h : exec ks s = some s₁) :
    exec (ks ++ ks') s = exec ks' s₁ := by
  rw [exec_append, h]; rfl

lemma exec_snoc_of {ks ks' : List Call} {s s₀ s₁ : State} (h0 : exec ks s = some s₀)
    (h1 : exec ks' s₀ = some s₁) : exec (ks ++ ks') s = some s₁ := by
  rw [exec_split h0]; exact h1

lemma exec_singleton (k : Call) (s : State) : exec [k] s = step k s := by
  simp only [exec]
  cases step k s <;> rfl

lemma step_of_exec {k : Call} {s s' : State} (h : exec [k] s = some s') : step k s = some s' := by
  rw [← exec_singleton]; exact h

lemma step_none_of_exec {k : Call} {s : State} (h : (exec [k] s).isSome = false) :
    step k s = none := by
  rw [← exec_singleton]; simpa using h

/-! ## The witness -/

theorem RotationWrappersRun : Properties.RotationWrappersRun := by
  obtain ⟨s₀, h0, he0⟩ := exists_run_of_isSome (ks := vtSetupCalls) (s := init) (by decide)
  refine ⟨s₀, ?_⟩
  obtain ⟨s, h1, he1⟩ := exists_run_of_isSome (s := s₀)
    (ks := [vtCall 1 vtAdmin (.removeValidatorRoles vtChain vtValidator
              ⟨false, true, false, false, false, false⟩),
            vtCall 1 vtAdmin (.addValidatorRoles vtChain vtValidator
              ⟨false, true, false, false, false, false⟩),
            vtCall 1 vtAdmin (.removeValidator vtChain vtValidator),
            vtCall 1 vtAdmin (.addValidatorForChainId 270 vtValidator),
            vtCall 1 vtAdmin (.removeValidatorForChainId 270 vtValidator)])
    (by rw [← exec_split he0]; decide)
  refine ⟨s, h0, map_of_exec he0 (fun s => s.members vtChain COMMITTER_ROLE vtValidator)
    (by decide), h1, ?_⟩
  have hall := map_of_exec (exec_eq_some_iff.mpr (run_append h0 h1))
    (fun s => removeValidatorParams.roles.all (fun r => !s.members vtChain r vtValidator))
    (b := true) (by decide)
  simpa using hall

end Contracts.ValidatorTimelock
