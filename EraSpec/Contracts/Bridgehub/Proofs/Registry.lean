import EraSpec.Contracts.Bridgehub.Properties.Registry

/-!
# Proofs: `L1Bridgehub`

Proofs of `EraSpec.Contracts.Bridgehub.Properties.Registry`.

The run-level results are inductions over `Run`. Each one-step lemma does a case split
over all 22 entry points and over every guard, so a new entry point or a changed guard
breaks the proof rather than slipping past it. Runs are also computed by
`bridgehubRunF`, which makes splitting a run at a call (`run_append_iff`) a list
induction.

The countermodels and witnesses are explicit runs from `init` in the deployment
`wRegistryCfg` of the Specs file, checked by kernel evaluation (`decide +kernel`).
-/

namespace Contracts.Bridgehub

/-! ## Runs as a function -/

/-- The run of `l` from `s`, as a function. -/
private def bridgehubRunF (cfg : Config) : State → List Call → Option State
  | s, [] => some s
  | s, k :: l => (exec cfg k.1 k.2 s).bind fun u => bridgehubRunF cfg u l

private lemma runF_append (cfg : Config) (s : State) (l₁ l₂ : List Call) :
    bridgehubRunF cfg s (l₁ ++ l₂) =
      (bridgehubRunF cfg s l₁).bind fun u => bridgehubRunF cfg u l₂ := by
  induction l₁ generalizing s with
  | nil => simp [bridgehubRunF]
  | cons k l ih =>
    simp only [List.cons_append, bridgehubRunF]
    cases exec cfg k.1 k.2 s with
    | none => simp
    | some u => simp [ih]

private lemma run_iff_runF (cfg : Config) (s t : State) (l : List Call) :
    Run cfg s l t ↔ bridgehubRunF cfg s l = some t := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | snoc k _ hx ih => simp [runF_append, ih, bridgehubRunF, hx]
  · induction l using List.reverseRecOn generalizing t with
    | nil => intro h; simp [bridgehubRunF] at h; subst h; exact Run.nil _
    | append_singleton l k ih =>
      intro h
      rw [runF_append] at h
      cases hl : bridgehubRunF cfg s l with
      | none => simp [hl] at h
      | some u =>
        simp only [hl, Option.bind_some, bridgehubRunF] at h
        cases hx : exec cfg k.1 k.2 u with
        | none => simp [hx] at h
        | some v =>
          simp [hx] at h; subst h
          exact Run.snoc k (ih u hl) hx

private lemma run_append_iff (cfg : Config) (s t : State) (l₁ l₂ : List Call) :
    Run cfg s (l₁ ++ l₂) t ↔ ∃ u, Run cfg s l₁ u ∧ Run cfg u l₂ t := by
  simp only [run_iff_runF, runF_append]
  cases bridgehubRunF cfg s l₁ <;> simp

private lemma run_single (cfg : Config) (s t : State) (k : Call) :
    Run cfg s [k] t ↔ exec cfg k.1 k.2 s = some t := by
  simp only [run_iff_runF, bridgehubRunF]
  cases exec cfg k.1 k.2 s <;> simp

/-- A state predicate preserved by every successful call holds at the end of every run. -/
private lemma Run.invariant {cfg : Config} (P : State → Prop)
    (hstep : ∀ caller a s s', P s → exec cfg caller a s = some s' → P s')
    {s t : State} {l : List Call} (h : Run cfg s l t) (hs : P s) : P t := by
  induction h with
  | nil => exact hs
  | snoc k _ hx ih => exact hstep _ _ _ _ ih hx

/-- The same, for a predicate that holds only along runs whose calls satisfy `Q`. -/
private lemma Run.invariantOn {cfg : Config} (Q : Call → Prop) (P : State → Prop)
    (hstep : ∀ caller a s s', Q (caller, a) → P s → exec cfg caller a s = some s' → P s')
    {s t : State} {l : List Call} (h : Run cfg s l t) (hq : ∀ k ∈ l, Q k) (hs : P s) : P t := by
  induction h with
  | nil => exact hs
  | snoc k _ hx ih =>
    exact hstep _ _ _ _ (hq k (by simp)) (ih fun k hk => hq k (by simp [hk])) hx

/-! ## Unfolding a successful call -/

private lemma registerNew_eq {cfg : Config} {s s' : State} {c : ChainId} {z : Address}
    {chk : Bool} :
    registerNew cfg s c z chk = some s' ↔
      ¬ (chk = true ∧ (insert c s.zkKeys).card > cfg.maxChains) ∧
      s' = { s with zkKeys := insert c s.zkKeys, zkAddr := Function.update s.zkAddr c z } := by
  unfold registerNew
  split_ifs with h <;> simp_all [eq_comm]

private lemma map_const_eq {α : Type} {o : Option α} {s s' : State} :
    o.map (fun _ => s) = some s' ↔ o.isSome ∧ s' = s := by
  cases o <;> simp [eq_comm]

/-- Normalise `exec … = some s'` for one entry point: split every guard, and substitute
the post-state. -/
macro "bridgehub_exec_unfold" h:ident : tactic => `(tactic| (
  simp only [exec, map_const_eq, writeChain] at $h:ident
  try split_ifs at $h:ident
  all_goals (try simp only [registerNew_eq] at $h:ident)
  all_goals (try (obtain ⟨_, hh⟩ := $h:ident; subst hh))
  all_goals (try (cases $h:ident))))

/-- Close a goal about a post-state: split the point updates, then simplify. -/
macro "bridgehub_upd_close" : tactic => `(tactic| (
  try simp only [Function.update_apply] at *
  try split_ifs at *
  all_goals (try subst_vars)
  all_goals simp_all [ValidChainParams, ZkGetOk, getZKChain]))

/-! ## Chain registration -/

private lemma step_ctm_ne {cfg : Config} {caller : Address} {a : Action} {s s' : State}
    {c : ChainId} (h : exec cfg caller a s = some s') (hc : s.chainTypeManager c ≠ 0) :
    s'.chainTypeManager c ≠ 0 := by
  cases a <;> bridgehub_exec_unfold h <;> bridgehub_upd_close

private lemma step_registers {cfg : Config} {caller : Address} {a : Action} {s s' : State}
    {c : ChainId} (h : exec cfg caller a s = some s') (hr : a.registers c = true) :
    s.chainTypeManager c = 0 ∧ s'.chainTypeManager c ≠ 0 := by
  cases a <;> simp only [Action.registers, decide_eq_true_eq, Bool.false_eq_true] at hr <;>
    subst hr <;> bridgehub_exec_unfold h <;> bridgehub_upd_close

/-- `Properties.CtmNeverCleared`, proved. -/
theorem CtmNeverCleared : Properties.CtmNeverCleared := by
  intro cfg s t l h c hc
  exact Run.invariant (fun u => u.chainTypeManager c ≠ 0)
    (fun _ _ _ _ hp hx => step_ctm_ne hx hp) h hc

/-- `Properties.ChainIdRegisteredOnce`, proved. -/
theorem ChainIdRegisteredOnce : Properties.ChainIdRegisteredOnce := by
  intro cfg s t l h c
  suffices H : (l.filter fun k => k.2.registers c).length ≤ 1 ∧
      (s.chainTypeManager c ≠ 0 → (l.filter fun k => k.2.registers c) = []) ∧
      ((l.filter fun k => k.2.registers c) ≠ [] → t.chainTypeManager c ≠ 0) from ⟨H.1, H.2.1⟩
  induction h with
  | nil => simp
  | @snoc t u l k hrun hx ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    by_cases hk : k.2.registers c = true
    · obtain ⟨h0, h1⟩ := step_registers hx hk
      have hl : (l.filter fun k => k.2.registers c) = [] := by
        by_contra hne; exact ih3 hne h0
      refine ⟨by simp [List.filter_append, hl, hk], ?_, fun _ => h1⟩
      intro hs
      exact absurd h0 (CtmNeverCleared cfg s t l hrun c hs)
    · have hk' : k.2.registers c = false := by simpa using hk
      simp only [List.filter_append, List.filter_cons, List.filter_nil, hk', Bool.false_eq_true,
        ite_false, List.append_nil]
      exact ⟨ih1, ih2, fun hne => step_ctm_ne hx (ih3 hne)⟩

private lemma step_baseRegistered {cfg : Config} {caller : Address} {a : Action} {s s' : State}
    (h : exec cfg caller a s = some s')
    (hp : ∀ c, s.chainTypeManager c ≠ 0 → s.assetIdRegistered (s.baseTokenAssetId c) = true) :
    ∀ c, s'.chainTypeManager c ≠ 0 → s'.assetIdRegistered (s'.baseTokenAssetId c) = true := by
  intro c
  cases a <;> bridgehub_exec_unfold h <;> bridgehub_upd_close

/-- `Properties.ChainBaseTokenRegistered`, proved. -/
theorem ChainBaseTokenRegistered : Properties.ChainBaseTokenRegistered := by
  rintro cfg s ⟨o, l, h⟩
  exact Run.invariant (fun u => ∀ c, u.chainTypeManager c ≠ 0 →
      u.assetIdRegistered (u.baseTokenAssetId c) = true)
    (fun _ _ _ _ hp hx => step_baseRegistered hx hp) h (fun c hc => absurd rfl hc)

private lemma step_approved {cfg : Config} {caller : Address} {a : Action} {s s' : State}
    (A : Address → Prop) (h : exec cfg caller a s = some s')
    (h1 : ∀ m, s.ctmRegistered m = true → A m)
    (h2 : ∀ id, s.ctmAssetIdToAddress id ≠ 0 → A (s.ctmAssetIdToAddress id))
    (h3 : ∀ c, s.chainTypeManager c ≠ 0 → A (s.chainTypeManager c))
    (hadd : ∀ m, a = .addChainTypeManager m → A m) :
    (∀ m, s'.ctmRegistered m = true → A m) ∧
    (∀ id, s'.ctmAssetIdToAddress id ≠ 0 → A (s'.ctmAssetIdToAddress id)) ∧
    (∀ c, s'.chainTypeManager c ≠ 0 → A (s'.chainTypeManager c)) := by
  cases a <;> bridgehub_exec_unfold h <;>
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩ <;> bridgehub_upd_close

/-- `Properties.ChainCtmWasApproved`, proved. -/
theorem ChainCtmWasApproved : Properties.ChainCtmWasApproved := by
  intro cfg o l s h
  suffices H : (∀ m, s.ctmRegistered m = true →
        ∃ caller, (caller, Action.addChainTypeManager m) ∈ l) ∧
      (∀ id, s.ctmAssetIdToAddress id ≠ 0 →
        ∃ caller, (caller, Action.addChainTypeManager (s.ctmAssetIdToAddress id)) ∈ l) ∧
      (∀ c, s.chainTypeManager c ≠ 0 →
        ∃ caller, (caller, Action.addChainTypeManager (s.chainTypeManager c)) ∈ l) from H.2.2
  induction h with
  | nil => simp [init]
  | @snoc t u l k _ hx ih =>
    have mono : ∀ m, (∃ caller, (caller, Action.addChainTypeManager m) ∈ l) →
        ∃ caller, (caller, Action.addChainTypeManager m) ∈ l ++ [k] :=
      fun m ⟨c', hc'⟩ => ⟨c', List.mem_append_left _ hc'⟩
    exact step_approved (fun m => ∃ caller, (caller, Action.addChainTypeManager m) ∈ l ++ [k]) hx
      (fun m hm => mono m (ih.1 m hm)) (fun id hid => mono _ (ih.2.1 id hid))
      (fun c hc => mono _ (ih.2.2 c hc))
      (fun m hm => ⟨k.1, by simp [← hm]⟩)

private lemma step_fixed {cfg : Config} {caller : Address} {a : Action} {s s' : State}
    {c : ChainId} (h : exec cfg caller a s = some s') (hm : a.bridgeMintFor c = false)
    (hc : s.chainTypeManager c ≠ 0) :
    s'.chainTypeManager c = s.chainTypeManager c ∧
      s'.baseTokenAssetId c = s.baseTokenAssetId c := by
  cases a <;> simp only [Action.bridgeMintFor, decide_eq_false_iff_not] at hm <;>
    bridgehub_exec_unfold h <;> bridgehub_upd_close

/-- `Properties.CtmAndBaseTokenFixedOutsideBridgeMint`, proved. -/
theorem CtmAndBaseTokenFixedOutsideBridgeMint :
    Properties.CtmAndBaseTokenFixedOutsideBridgeMint := by
  intro cfg s t l h c hl hc
  exact Run.invariantOn (fun k => k.2.bridgeMintFor c = false)
    (fun u => u.chainTypeManager c = s.chainTypeManager c ∧
      u.baseTokenAssetId c = s.baseTokenAssetId c)
    (fun _ _ _ _ hq hp hx => by
      obtain ⟨e1, e2⟩ := step_fixed hx hq (hp.1 ▸ hc)
      exact ⟨e1.trans hp.1, e2.trans hp.2⟩) h hl ⟨rfl, rfl⟩

private lemma step_consistent {cfg : Config} {caller : Address} {a : Action} {s s' : State}
    (h : exec cfg caller a s = some s') (hq : a.handlerRegistryWrite = false)
    (hp : ∀ c, (c ∈ s.zkKeys ↔ s.chainTypeManager c ≠ 0) ∧ (c ∈ s.zkKeys ↔ s.zkAddr c ≠ 0)) :
    ∀ c, (c ∈ s'.zkKeys ↔ s'.chainTypeManager c ≠ 0) ∧ (c ∈ s'.zkKeys ↔ s'.zkAddr c ≠ 0) := by
  intro c
  have hc := hp c
  cases a <;> simp only [Action.handlerRegistryWrite, Bool.true_eq_false] at hq <;>
    bridgehub_exec_unfold h <;> bridgehub_upd_close

/-- `Properties.RegistryConsistentWithoutHandler`, proved. -/
theorem RegistryConsistentWithoutHandler : Properties.RegistryConsistentWithoutHandler := by
  intro cfg o l s h hl
  exact Run.invariantOn (fun k => k.2.handlerRegistryWrite = false)
    (fun u => ∀ c, (c ∈ u.zkKeys ↔ u.chainTypeManager c ≠ 0) ∧ (c ∈ u.zkKeys ↔ u.zkAddr c ≠ 0))
    (fun _ _ _ _ hq hp hx => step_consistent hx hq hp) h hl (fun c => by simp [init])

private lemma step_card {cfg : Config} {caller : Address} {a : Action} {s s' : State}
    (h : exec cfg caller a s = some s') (hq : a.uncheckedRegistration = false)
    (hp : s.zkKeys.card ≤ cfg.maxChains) : s'.zkKeys.card ≤ cfg.maxChains := by
  cases a <;> simp only [Action.uncheckedRegistration, Bool.not_eq_false'] at hq <;>
    bridgehub_exec_unfold h <;> simp_all

/-- `Properties.ChainCountBounded`, proved. -/
theorem ChainCountBounded : Properties.ChainCountBounded := by
  intro cfg o l s h hl
  exact Run.invariantOn (fun k => k.2.uncheckedRegistration = false)
    (fun u => u.zkKeys.card ≤ cfg.maxChains)
    (fun _ _ _ _ hq hp hx => step_card hx hq hp) h hl (by simp [init])

/-- The logged round-trip invariant after the calls `l`: every set
`ctmAssetIdFromAddress[m]` is the encoding of `m` with the sender of a logged
`setCTMAssetAddress(m, m)`, and it round-trips unless the run has a logged collision at
`m`. -/
private def RoundTripInv (cfg : Config) (l : List Call) (s : State) : Prop :=
  ∀ m, s.ctmAssetIdFromAddress m ≠ 0 →
    (∃ c₁, (c₁, Action.setCTMAssetAddress m m) ∈ l ∧
      s.ctmAssetIdFromAddress m = cfg.encodeAssetId cfg.thisChain m c₁) ∧
    (s.ctmAssetIdToAddress (s.ctmAssetIdFromAddress m) = m ∨ CtmAssetIdLoggedCollision cfg l m)

private lemma collision_mono {cfg : Config} {l : List Call} {m : Address} (k : Call)
    (h : CtmAssetIdLoggedCollision cfg l m) : CtmAssetIdLoggedCollision cfg (l ++ [k]) m := by
  obtain ⟨c₁, c₂, m', h1, h2, hne, heq⟩ := h
  exact ⟨c₁, c₂, m', List.mem_append_left _ h1, List.mem_append_left _ h2, hne, heq⟩

private lemma step_roundTrip {cfg : Config} {l : List Call} {caller : Address} {a : Action}
    {s s' : State} (h : exec cfg caller a s = some s') (hq : a.ctmAssetDisciplined = true)
    (hp : RoundTripInv cfg l s) : RoundTripInv cfg (l ++ [(caller, a)]) s' := by
  have lift : ∀ m, (∃ c₁, (c₁, Action.setCTMAssetAddress m m) ∈ l ∧
      s.ctmAssetIdFromAddress m = cfg.encodeAssetId cfg.thisChain m c₁) →
      ∃ c₁, (c₁, Action.setCTMAssetAddress m m) ∈ l ++ [(caller, a)] ∧
        s.ctmAssetIdFromAddress m = cfg.encodeAssetId cfg.thisChain m c₁ :=
    fun m ⟨c₁, hm, he⟩ => ⟨c₁, List.mem_append_left _ hm, he⟩
  cases a with
  | setCTMAssetAddress d m₀ =>
    simp only [Action.ctmAssetDisciplined, decide_eq_true_eq] at hq
    subst hq
    bridgehub_exec_unfold h
    intro m hm
    simp only [Function.update_apply] at hm ⊢
    by_cases hmm : m = d
    · subst hmm
      exact ⟨⟨caller, by simp, by simp⟩, Or.inl (by simp)⟩
    · simp only [hmm, ite_false] at hm ⊢
      obtain ⟨⟨c₁, hc₁, hdep⟩, hrt⟩ := hp m hm
      refine ⟨⟨c₁, List.mem_append_left _ hc₁, hdep⟩, ?_⟩
      by_cases hid : s.ctmAssetIdFromAddress m = cfg.encodeAssetId cfg.thisChain d caller
      · exact Or.inr ⟨c₁, caller, d, List.mem_append_left _ hc₁, by simp, Ne.symm hmm,
          hdep.symm.trans hid⟩
      · simp only [hid, ite_false]
        exact hrt.imp_right (collision_mono _)
  | _ =>
    bridgehub_exec_unfold h <;>
      exact fun m hm => ⟨lift m (hp m hm).1, (hp m hm).2.imp_right (collision_mono _)⟩

/-- `Properties.CtmAssetIdRoundTrip`, proved. -/
theorem CtmAssetIdRoundTrip : Properties.CtmAssetIdRoundTrip := by
  intro cfg o l s h hl
  suffices H : RoundTripInv cfg l s from fun m hm => (H m hm).2
  induction h with
  | nil => intro m hm; exact absurd rfl hm
  | @snoc t u l k _ hx ih =>
    exact step_roundTrip (a := k.2) (caller := k.1) hx (hl k (by simp))
      (ih fun k hk => hl k (by simp [hk]))

/-! ## The chain map -/

private lemma step_keys_mono {cfg : Config} {caller : Address} {a : Action} {s s' : State}
    (h : exec cfg caller a s = some s') {c : ChainId} (hc : c ∈ s.zkKeys) : c ∈ s'.zkKeys := by
  cases a <;> bridgehub_exec_unfold h <;> simp_all

private lemma step_addr_key {cfg : Config} {caller : Address} {a : Action} {s s' : State}
    (h : exec cfg caller a s = some s') (hp : ∀ c, s.zkAddr c ≠ 0 → c ∈ s.zkKeys) :
    ∀ c, s'.zkAddr c ≠ 0 → c ∈ s'.zkKeys := by
  intro c
  have hpc := hp c
  cases a <;> bridgehub_exec_unfold h <;> bridgehub_upd_close

private lemma reachable_addr_key {cfg : Config} {s : State} (hs : Reachable cfg s) :
    ∀ c, s.zkAddr c ≠ 0 → c ∈ s.zkKeys := by
  obtain ⟨o, l, h⟩ := hs
  exact Run.invariant (fun u => ∀ c, u.zkAddr c ≠ 0 → c ∈ u.zkKeys)
    (fun _ _ _ _ hp hx => step_addr_key hx hp) h (fun c hc => absurd rfl hc)

/-- `Properties.ChainMapOnlyGrows`, proved. -/
theorem ChainMapOnlyGrows : Properties.ChainMapOnlyGrows := by
  refine ⟨fun cfg s t l h c hc =>
    Run.invariant (fun u => c ∈ u.zkKeys) (fun _ _ _ _ hp hx => step_keys_mono hx hp) h hc, ?_⟩
  intro cfg s hs c
  have := reachable_addr_key hs c
  unfold ZkGetOk
  tauto

/-- `Properties.DiamondChangesOnlyByRegistration`, proved. -/
theorem DiamondChangesOnlyByRegistration : Properties.DiamondChangesOnlyByRegistration := by
  intro cfg caller a s s' c h hne
  cases a with
  | registerNewZKChain c₀ z chk =>
    bridgehub_exec_unfold h
    rename_i hauth _
    by_cases hc : c = c₀
    · subst hc; exact Or.inl ⟨z, chk, rfl, by simpa using hauth⟩
    · simp [getZKChain, hc] at hne
  | createNewChain c₀ m a₀ adm dep =>
    bridgehub_exec_unfold h
    rename_i hauth _ hvalid _ _
    by_cases hc : c = c₀
    · subst hc
      refine Or.inr ⟨by simp [Action.registers], hvalid.2.2.2.2.2.2.2.2.2, ?_⟩
      by_cases ho : caller = s.owner
      · exact Or.inl ho
      · exact Or.inr (by simp_all)
    · simp [getZKChain, hc] at hne
  | registerAlreadyDeployed c₀ z info =>
    bridgehub_exec_unfold h
    rename_i hauth _ _ _ _ hvalid _
    by_cases hc : c = c₀
    · subst hc
      exact Or.inr ⟨by simp [Action.registers], hvalid.2.2.2.2.2.2.2.2.2,
        Or.inl (by simpa using hauth)⟩
    · simp [getZKChain, hc] at hne
  | _ => bridgehub_exec_unfold h <;> simp_all [getZKChain]

/-- `Properties.DiamondFixedAfterRegistration`, proved. -/
theorem DiamondFixedAfterRegistration : Properties.DiamondFixedAfterRegistration := by
  intro cfg s t l h c hl hc
  have H := Run.invariantOn (fun k => k.2.handlerRegistersFor c = false)
    (fun u => getZKChain u c = getZKChain s c ∧ u.chainTypeManager c ≠ 0)
    (fun caller a u u' hq hp hx => by
      refine ⟨?_, step_ctm_ne hx hp.2⟩
      by_contra hne
      have hne' : getZKChain u' c ≠ getZKChain u c := fun he => hne (he.trans hp.1)
      rcases DiamondChangesOnlyByRegistration cfg caller a u u' c hx hne' with
        ⟨z, chk, rfl, -⟩ | ⟨-, h0, -⟩
      · simp [Action.handlerRegistersFor] at hq
      · exact hp.2 h0) h hl ⟨rfl, hc⟩
  exact H.1

/-! ## Settlement layers -/

private lemma step_whitelisted {cfg : Config} {caller : Address} {a : Action} {s s' : State}
    (h : exec cfg caller a s = some s')
    (hp : ∀ c, s.whitelistedSL c = true → c = cfg.thisChain ∨
      s.settlementLayer c = cfg.thisChain) :
    ∀ c, s'.whitelistedSL c = true → c = cfg.thisChain ∨
      s'.settlementLayer c = cfg.thisChain := by
  intro c hc
  have hpc := hp c
  cases a <;> bridgehub_exec_unfold h <;> bridgehub_upd_close

/-- `Properties.WhitelistedSettlementLayersSettleHere`, proved. -/
theorem WhitelistedSettlementLayersSettleHere :
    Properties.WhitelistedSettlementLayersSettleHere := by
  rintro cfg s ⟨o, l, h⟩
  exact Run.invariant (fun u => ∀ c, u.whitelistedSL c = true →
      c = cfg.thisChain ∨ u.settlementLayer c = cfg.thisChain)
    (fun _ _ _ _ hp hx => step_whitelisted hx hp) h (fun c hc => by simp_all [init])

/-- `Properties.MigrationOutOnlyToWhitelisted`, proved. -/
theorem MigrationOutOnlyToWhitelisted : Properties.MigrationOutOnlyToWhitelisted := by
  intro cfg caller a s s' c h hne hthis
  cases a <;> bridgehub_exec_unfold h <;> bridgehub_upd_close

/-! ## Registration effects, and what holds while a chain settles here -/

/-- `Properties.CreateNewChainPostcondition`, proved. -/
theorem CreateNewChainPostcondition : Properties.CreateNewChainPostcondition := by
  intro cfg caller s s' c m a adm d h
  bridgehub_exec_unfold h
  rename_i hauth hpause hvalid hdep hlim
  obtain ⟨h1, h2, h3, -, h5, h6, h7, h8, -, h10⟩ := hvalid
  refine ⟨by tauto, by simpa using hpause, h1, h2, h3, h10, h5, h7, h6, h8, by simp, by simp,
    by simp, by simp [getZKChain], hdep, by simpa using hlim, fun c' hc' => ?_⟩
  simp [getZKChain, hc']

/-- `Properties.RegisterDeployedPostcondition`, proved. -/
theorem RegisterDeployedPostcondition : Properties.RegisterDeployedPostcondition := by
  intro cfg caller s s' c z info h
  bridgehub_exec_unfold h
  rename_i hauth hz hkey hcid hbh hvalid hlim
  obtain ⟨h1, h2, h3, -, h5, h6, h7, h8, -, h10⟩ := hvalid
  refine ⟨by simpa using hauth, by simpa using hcid, by simpa using hbh, hkey, h10, h1, h2, h3,
    h5, h7, h6, h8, by simp, by simp, by simp, by simp [getZKChain], hz, by simpa using hlim,
    fun c' hc' => ?_⟩
  simp [getZKChain, hc']

private lemma step_assetReg {cfg : Config} {caller : Address} {a : Action} {s s' : State}
    {x : AssetId} (h : exec cfg caller a s = some s') (hx : s.assetIdRegistered x = true) :
    s'.assetIdRegistered x = true := by
  cases a <;> bridgehub_exec_unfold h <;> bridgehub_upd_close

/-- `Properties.AssetIdNeverUnregistered`, proved. -/
theorem AssetIdNeverUnregistered : Properties.AssetIdNeverUnregistered := by
  have H : ∀ (cfg : Config) (s t : State) (l : List Call), Run cfg s l t →
      ∀ a, s.assetIdRegistered a = true → t.assetIdRegistered a = true :=
    fun cfg s t l h a ha => Run.invariant (fun u => u.assetIdRegistered a = true)
      (fun _ _ _ _ hp hx => step_assetReg hx hp) h ha
  refine ⟨H, ?_⟩
  rintro cfg s ⟨o, l, h⟩
  exact H cfg _ s l h _ (by simp [init])

private lemma step_fixedHere {cfg : Config} {caller : Address} {a : Action} {s s' : State}
    {c : ChainId} (h : exec cfg caller a s = some s') (hb : a.burnFor c = false)
    (hc : s.chainTypeManager c ≠ 0) (hsl : s.settlementLayer c = cfg.thisChain) :
    s'.chainTypeManager c = s.chainTypeManager c ∧
      s'.baseTokenAssetId c = s.baseTokenAssetId c ∧
      s'.settlementLayer c = cfg.thisChain := by
  cases a <;> simp only [Action.burnFor, decide_eq_false_iff_not] at hb <;>
    bridgehub_exec_unfold h <;> bridgehub_upd_close

/-- `Properties.CtmAndBaseTokenFixedWhileSettlingHere`, proved. -/
theorem CtmAndBaseTokenFixedWhileSettlingHere :
    Properties.CtmAndBaseTokenFixedWhileSettlingHere := by
  intro cfg s t l h c hl hc hsl
  exact Run.invariantOn (fun k => k.2.burnFor c = false)
    (fun u => u.chainTypeManager c = s.chainTypeManager c ∧
      u.baseTokenAssetId c = s.baseTokenAssetId c ∧ u.settlementLayer c = cfg.thisChain)
    (fun _ _ _ _ hq hp hx => by
      obtain ⟨e1, e2, e3⟩ := step_fixedHere hx hq (hp.1 ▸ hc) hp.2.2
      exact ⟨e1.trans hp.1, e2.trans hp.2.1, e3⟩) h hl ⟨rfl, rfl, hsl⟩

/-! ## Settlement layers, run level -/

private lemma step_sl {cfg : Config} {caller : Address} {a : Action} {s s' : State}
    (h : exec cfg caller a s = some s') (c : ChainId) :
    s'.settlementLayer c = s.settlementLayer c ∨ s'.settlementLayer c = cfg.thisChain ∨
      (a = .burnSetSettlementLayer c (s'.settlementLayer c) ∧ s'.settlementLayer c ≠ c) := by
  cases a with
  | burnSetSettlementLayer c₀ sl =>
    bridgehub_exec_unfold h
    rename_i hauth hwl hsl hwc hget
    by_cases hc : c = c₀
    · subst hc
      refine Or.inr (Or.inr ⟨by simp, ?_⟩)
      simp only [Function.update_self]
      rintro rfl
      exact hwc (by simpa using hwl)
    · exact Or.inl (by simp [hc])
  | _ => bridgehub_exec_unfold h <;> bridgehub_upd_close

/-- `Properties.RemoteSettlementLayerCameFromBurn`, proved. -/
theorem RemoteSettlementLayerCameFromBurn : Properties.RemoteSettlementLayerCameFromBurn := by
  intro cfg o l s h
  induction h with
  | nil => intro c hc; exact absurd rfl hc
  | @snoc t u l k _ hx ih =>
    intro c h0 hthis
    rcases step_sl hx c with he | he | ⟨he, hne⟩
    · rw [he] at h0 hthis ⊢
      obtain ⟨h1, caller, hmem⟩ := ih c h0 hthis
      exact ⟨h1, caller, List.mem_append_left _ hmem⟩
    · exact absurd he hthis
    · exact ⟨hne, k.1, by simp [← he]⟩

/-- `Properties.MigrationTargetSettlesHere`, proved. -/
theorem MigrationTargetSettlesHere : Properties.MigrationTargetSettlesHere := by
  intro cfg s s' caller c sl hreach h
  have hw := WhitelistedSettlementLayersSettleHere cfg s hreach sl
  bridgehub_exec_unfold h
  rename_i hauth hwl hsl hwc hget
  have hwl' : s.whitelistedSL sl = true := by simpa using hwl
  refine ⟨by simp, ?_⟩
  rcases hw hwl' with h1 | h1
  · exact Or.inl h1
  · right
    have hne : sl ≠ c := by rintro rfl; exact hwc hwl'
    simp [hne, h1]

/-! ## Requests -/

/-- `Properties.DirectRequestAccounting`, proved. -/
theorem DirectRequestAccounting : Properties.DirectRequestAccounting := by
  intro cfg s caller env req o h
  unfold requestDirect at h
  split_ifs at h
  cases h
  simp_all [refundOf]
  split_ifs <;> simp_all

/-- `Properties.TwoBridgesRequestAccounting`, proved. -/
theorem TwoBridgesRequestAccounting : Properties.TwoBridgesRequestAccounting := by
  intro cfg s caller env req reply o h
  unfold requestTwoBridges at h
  split_ifs at h <;> cases h <;> simp_all [refundOf]

private lemma request_facts {cfg : Config} {s : State} {caller : Address} {env : CallEnv}
    {o : Outcome} {c : ChainId}
    (h : (∃ req : DirectRequest, req.chainId = c ∧ requestDirect cfg s caller env req = some o) ∨
       (∃ (req : TwoBridgesRequest) (reply : SecondBridgeReply), req.chainId = c ∧
          requestTwoBridges cfg s caller env req reply = some o)) :
    ZkGetOk s c ∧ o.target = s.zkAddr c ∧ o.depositAssetId = s.baseTokenAssetId c := by
  rcases h with ⟨req, rfl, h⟩ | ⟨req, reply, rfl, h⟩
  · obtain ⟨-, h1, -, h2, -, -, -, -, -, h3, -⟩ :=
      DirectRequestAccounting cfg s caller env req o h
    exact ⟨h1, h3, h2⟩
  · obtain ⟨-, h1, -, h2, -, -, -, -, -, h3, -⟩ :=
      TwoBridgesRequestAccounting cfg s caller env req reply o h
    exact ⟨h1, h3, h2⟩

/-- `Properties.RequestsReachRegisteredChains`, proved. -/
theorem RequestsReachRegisteredChains : Properties.RequestsReachRegisteredChains := by
  intro cfg o l s h hl caller env out c hreq
  obtain ⟨hok, ht, hd⟩ := request_facts hreq
  obtain ⟨hc1, hc2⟩ := RegistryConsistentWithoutHandler cfg o l s h hl c
  have hkey : c ∈ s.zkKeys := by
    rcases hok with hz | hk
    · exact hc2.2 hz
    · exact hk
  refine ⟨hc1.1 hkey, ht ▸ hc2.1 hkey, by simp [ht, getZKChain], ?_⟩
  rw [hd]
  exact ChainBaseTokenRegistered cfg s ⟨o, l, h⟩ c (hc1.1 hkey)

/-- `Properties.RequestNeedsMapEntry`, proved. -/
theorem RequestNeedsMapEntry : Properties.RequestNeedsMapEntry := by
  intro cfg s hs caller env o c hreq
  obtain ⟨hok, ht, -⟩ := request_facts hreq
  exact ⟨(ChainMapOnlyGrows.2 cfg s hs c).1 hok, by simp [ht, getZKChain]⟩

private lemma exec_create {cfg : Config} {caller : Address} {c : ChainId} {m : Address}
    {a : AssetId} {adm d : Address} {s s' : State}
    (h : exec cfg caller (.createNewChain c m a adm d) s = some s') :
    s'.chainTypeManager c = m ∧ m ≠ 0 ∧ s'.baseTokenAssetId c = a ∧ s'.zkAddr c = d := by
  bridgehub_exec_unfold h; simp_all [ValidChainParams]

/-- `Properties.RequestChargesCreationBaseToken`, proved. -/
theorem RequestChargesCreationBaseToken : Properties.RequestChargesCreationBaseToken := by
  intro cfg s t l₁ l₂ caller₀ c m a adm d h hl₂ caller env o hreq
  obtain ⟨v, hv, h2⟩ := (run_append_iff cfg s t _ l₂).1 h
  obtain ⟨u, -, hk⟩ := (run_append_iff cfg s v l₁ _).1 hv
  obtain ⟨hm, hm0, ha, hd⟩ := exec_create ((run_single cfg u v _).1 hk)
  obtain ⟨-, ht, hdep⟩ := request_facts hreq
  have hctm : v.chainTypeManager c ≠ 0 := hm ▸ hm0
  have hfix := CtmAndBaseTokenFixedOutsideBridgeMint cfg v t l₂ h2 c hl₂ hctm
  refine ⟨by rw [hdep, hfix.2, ha], fun hl => ?_⟩
  have := DiamondFixedAfterRegistration cfg v t l₂ h2 c hl hctm
  simp only [getZKChain] at this
  rw [ht, this, hd]

/-! ## Authority and pause -/

/-- `Properties.RegistryWritesAuthorized`, proved. -/
theorem RegistryWritesAuthorized : Properties.RegistryWritesAuthorized := by
  intro cfg caller a s s' h
  cases a <;> bridgehub_exec_unfold h <;> simp_all <;> tauto

/-- `Properties.PauseBlocksCreationAndRequests`, proved. -/
theorem PauseBlocksCreationAndRequests : Properties.PauseBlocksCreationAndRequests := by
  intro cfg s hp caller
  exact ⟨fun _ _ _ _ _ => by simp [exec, hp], fun _ _ => by simp [requestDirect, hp],
    fun _ _ _ => by simp [requestTwoBridges, hp]⟩

/-! ## Countermodels and witnesses

All use the deployment `wRegistryCfg` and runs from `init wRegistryCfg 1`. The concrete
facts are computed by the kernel; a run is turned into `Run` by `run_iff_runF`. -/

private lemma reach_of_runF {cfg : Config} {o : Address} {l : List Call} {s : State}
    (h : bridgehubRunF cfg (init cfg o) l = some s) : Reachable cfg s :=
  ⟨o, l, (run_iff_runF _ _ _ _).2 h⟩

private lemma any_some {α : Type} {p : α → Bool} {x : Option α} (h : x.any p = true) :
    ∃ a, x = some a ∧ p a = true := by
  cases x <;> simp_all

/-- `wRegistryCfg`'s asset-id hash `d + 100` is injective in the data, so no run has a
logged collision. -/
private lemma wRegistry_no_collision (l : List Call) (m : Address) :
    ¬ CtmAssetIdLoggedCollision wRegistryCfg l m := by
  rintro ⟨c₁, c₂, m', -, -, hne, heq⟩
  exact hne (add_right_cancel heq).symm

/-- `Properties.BridgeMintRewritesBaseToken`, proved: at the end of `wRegistryRun` chain
`11` (CTM `60`, base token `7`) has migrated onto `10`, and the handler's
`forwardedBridgeMint(161, 11, 8)` sets its base token to `8`. -/
theorem BridgeMintRewritesBaseToken : Properties.BridgeMintRewritesBaseToken := by
  obtain ⟨s, hs, hP⟩ := any_some (p := fun (s : State) => decide (s.chainTypeManager 11 ≠ 0 ∧
      s.baseTokenAssetId 11 = 7) &&
      (exec wRegistryCfg 53 (.forwardedBridgeMint 161 11 8) s).any
        (fun (s' : State) => decide (s'.baseTokenAssetId 11 = 8)))
    (x := bridgehubRunF wRegistryCfg (init wRegistryCfg 1) wRegistryRun) (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
  obtain ⟨⟨h1, h2⟩, h3⟩ := hP
  obtain ⟨s', hx, hb⟩ := any_some h3
  exact ⟨wRegistryCfg, s, s', 53, 161, 11, 8, reach_of_runF hs, h1, by rw [h2]; decide, hx,
    by simpa using hb⟩

/-- `Properties.RemovedCtmStillAssignedByBridgeMint`, proved: after `wRegistryPrelude` the
owner removes CTM `60`; the handler's `forwardedBridgeMint(160, 14, 7)` makes `60` the CTM
of chain `14`. -/
theorem RemovedCtmStillAssignedByBridgeMint : Properties.RemovedCtmStillAssignedByBridgeMint := by
  obtain ⟨s, hs, hP⟩ := any_some (p := fun (s : State) => decide (s.ctmRegistered 60 = false ∧
      s.chainTypeManager 14 = 0) &&
      (exec wRegistryCfg 53 (.forwardedBridgeMint 160 14 7) s).any
        (fun (s' : State) => decide (s'.chainTypeManager 14 = 60)))
    (x := bridgehubRunF wRegistryCfg (init wRegistryCfg 1)
      (wRegistryPrelude ++ [(1, .removeChainTypeManager 60)])) (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
  obtain ⟨⟨h1, h2⟩, h3⟩ := hP
  obtain ⟨s', hx, hc⟩ := any_some h3
  exact ⟨wRegistryCfg, s, s', 53, 160, 14, 7, 60, reach_of_runF hs, h1, h2, hx,
    by simpa using hc, by decide⟩

/-- `Properties.HandlerEntryOverwrittenByCreate`, proved: after `wRegistryPrelude` the
handler registers chain `14` with diamond `80`; `createNewChain(14, 60, 7, 0)` with the
CTM returning `74` then succeeds and stores `74`. -/
theorem HandlerEntryOverwrittenByCreate : Properties.HandlerEntryOverwrittenByCreate := by
  obtain ⟨s, hs, hP⟩ := any_some (p := fun (s : State) => decide ((14 : ChainId) ∈ s.zkKeys ∧
      s.chainTypeManager 14 = 0 ∧ s.zkAddr 14 = 80) &&
      (exec wRegistryCfg 1 (.createNewChain 14 60 7 0 74) s).any
        (fun (s' : State) => decide (s'.zkAddr 14 = 74)))
    (x := bridgehubRunF wRegistryCfg (init wRegistryCfg 1)
      (wRegistryPrelude ++ [(53, .registerNewZKChain 14 80 true)])) (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hP
  obtain ⟨s', hx, hz⟩ := any_some h4
  exact ⟨wRegistryCfg, s, s', 1, 14, 60, 7, 0, 74, reach_of_runF hs, h1, h2,
    by rw [h3]; decide, hx, by simpa using hz, by rw [h3]; decide⟩

/-- `Properties.CtmAssetIdRoundTripNeedsDiscipline`, proved: two `setCTMAssetAddress`
calls by the CTM deployer with data `5`, for CTMs `60` and `61`. -/
theorem CtmAssetIdRoundTripNeedsDiscipline : Properties.CtmAssetIdRoundTripNeedsDiscipline := by
  let l : List Call := [(1, .setAddresses 50 51 52 53 54), (1, .addChainTypeManager 60),
    (1, .addChainTypeManager 61), (51, .setCTMAssetAddress 5 60), (51, .setCTMAssetAddress 5 61)]
  obtain ⟨s, hs, hP⟩ := any_some (p := fun (s : State) => decide (s.ctmAssetIdFromAddress 60 ≠ 0 ∧
      s.ctmAssetIdToAddress (s.ctmAssetIdFromAddress 60) ≠ 60))
    (x := bridgehubRunF wRegistryCfg (init wRegistryCfg 1) l) (by decide +kernel)
  simp only [decide_eq_true_eq] at hP
  exact ⟨wRegistryCfg, l, s, 60, fun x y d d' h => add_right_cancel h,
    (run_iff_runF _ _ _ _).2 hs, wRegistry_no_collision l 60, hP.1, hP.2⟩

/-- `wRegistryCfg` with an asset-id hash that maps the data `60` and `61` to the same id
`160` and any other data `d` to `d + 100`: in the data it collides only on that pair. -/
private def wRegistryCollidingCfg : Config :=
  { wRegistryCfg with encodeAssetId := fun _ d _ => if d = 61 then 160 else d + 100 }

/-- `Properties.CtmAssetIdCollisionFires`, proved: under `wRegistryCollidingCfg` the CTM
deployer sets CTM `60`'s asset id, then CTM `61`'s; both are `160`, so
`ctmAssetIdToAddress[160] = 61` while `ctmAssetIdFromAddress[60] = 160`. -/
theorem CtmAssetIdCollisionFires : Properties.CtmAssetIdCollisionFires := by
  let l : List Call := [(1, .setAddresses 50 51 52 53 54), (1, .addChainTypeManager 60),
    (1, .addChainTypeManager 61), (51, .setCTMAssetAddress 60 60), (51, .setCTMAssetAddress 61 61)]
  have hl : ∀ k ∈ l, k.2.ctmAssetDisciplined = true := by decide +kernel
  obtain ⟨s, hs, hP⟩ := any_some (p := fun (s : State) => decide (s.ctmAssetIdFromAddress 60 ≠ 0 ∧
      s.ctmAssetIdToAddress (s.ctmAssetIdFromAddress 60) ≠ 60))
    (x := bridgehubRunF wRegistryCollidingCfg (init wRegistryCollidingCfg 1) l) (by decide +kernel)
  simp only [decide_eq_true_eq] at hP
  refine ⟨wRegistryCollidingCfg, l, s, 60, (run_iff_runF _ _ _ _).2 hs, hl, hP.1, hP.2,
    51, 51, 61, by simp [l], by simp [l], by decide, by decide +kernel⟩

/-- `Properties.HandlerRegisterReplacesDiamond`, proved: at the end of `wRegistryRun`
chain `12` has CTM `61` and diamond `72`; the handler's `registerNewZKChain(12, 82, true)`
stores `82`. -/
theorem HandlerRegisterReplacesDiamond : Properties.HandlerRegisterReplacesDiamond := by
  obtain ⟨s, hs, hP⟩ := any_some (p := fun (s : State) => decide (s.chainTypeManager 12 ≠ 0 ∧
      getZKChain s 12 = 72) &&
      (exec wRegistryCfg 53 (.registerNewZKChain 12 82 true) s).any
        (fun (s' : State) => decide (getZKChain s' 12 = 82)))
    (x := bridgehubRunF wRegistryCfg (init wRegistryCfg 1) wRegistryRun) (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
  obtain ⟨⟨h1, h2⟩, h3⟩ := hP
  obtain ⟨s', hx, hz⟩ := any_some h3
  exact ⟨wRegistryCfg, s, s', 53, 12, 82, true, reach_of_runF hs, h1, by rw [h2]; decide, hx,
    by simpa using hz, by rw [h2]; decide⟩

/-- `Properties.WithoutCheckWhitelistedLayerLeaves`, proved: chains `10` and `11` are both
whitelisted, and without the check chain `10` migrates onto `11`; with it the call reverts. -/
theorem WithoutCheckWhitelistedLayerLeaves : Properties.WithoutCheckWhitelistedLayerLeaves := by
  obtain ⟨s, hs, hP⟩ := any_some (p := fun (s : State) =>
      (burnNoSettlementLayerCheck wRegistryCfg 53 s 10 11).any
        (fun (s' : State) => decide (s'.whitelistedSL 10 = true ∧ s'.settlementLayer 10 ≠ 1)) &&
      (exec wRegistryCfg 53 (.burnSetSettlementLayer 10 11) s).isNone)
    (x := bridgehubRunF wRegistryCfg (init wRegistryCfg 1)
      (wRegistryPrelude ++ [wRegistryCreate10] ++ wRegistryRest ++
        [(1, .setSettlementLayerStatus 11 true)])) (by decide +kernel)
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hP
  obtain ⟨h1, h2⟩ := hP
  obtain ⟨s', hx, hb⟩ := any_some h1
  simp only [decide_eq_true_eq] at hb
  exact ⟨wRegistryCfg, s, s', 53, 10, 11, reach_of_runF hs, hx, hb.1, by decide, hb.2, h2⟩

/-- `Properties.WithoutCurrentSLCheckBaseTokenRewritten`, proved: at the end of
`wRegistryRun` chain `10` settles here with base token `7`; without the check the mint hook
sets it to `8`. -/
theorem WithoutCurrentSLCheckBaseTokenRewritten :
    Properties.WithoutCurrentSLCheckBaseTokenRewritten := by
  obtain ⟨s, hs, hP⟩ := any_some (p := fun (s : State) => decide (s.chainTypeManager 10 ≠ 0 ∧
      s.settlementLayer 10 = 1 ∧ s.baseTokenAssetId 10 = 7) &&
      (forwardedBridgeMintNoCurrentSLCheck wRegistryCfg 53 s 160 10 8).any
        (fun (s' : State) => decide (s'.baseTokenAssetId 10 = 8)) &&
      (exec wRegistryCfg 53 (.forwardedBridgeMint 160 10 8) s).isNone)
    (x := bridgehubRunF wRegistryCfg (init wRegistryCfg 1) wRegistryRun) (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at hP
  obtain ⟨⟨⟨h1, h2, h3⟩, h4⟩, h5⟩ := hP
  obtain ⟨s', hx, hb⟩ := any_some h4
  exact ⟨wRegistryCfg, s, s', 53, 160, 10, 8, reach_of_runF hs, h1, h2, by rw [h3]; decide, hx,
    by simpa using hb, h5⟩

/-- `Properties.WithoutAlreadyRegisteredCheckChainReRegistered`, proved: at the end of
`wRegistryRun` chain `11` has CTM `60`, base token `7` and diamond `71`; without the check
`createNewChain(11, 61, 8, 0)` with the CTM returning `72` succeeds again. -/
theorem WithoutAlreadyRegisteredCheckChainReRegistered :
    Properties.WithoutAlreadyRegisteredCheckChainReRegistered := by
  obtain ⟨s, hs, hP⟩ := any_some (p := fun (s : State) => decide (s.chainTypeManager 11 = 60 ∧
      s.baseTokenAssetId 11 = 7 ∧ s.zkAddr 11 = 71) &&
      (createNewChainNoDupCheck wRegistryCfg 1 s 11 61 8 72).any
        (fun (s' : State) => decide (s'.chainTypeManager 11 = 61 ∧
          s'.baseTokenAssetId 11 = 8 ∧ s'.zkAddr 11 = 72)) &&
      (exec wRegistryCfg 1 (.createNewChain 11 61 8 0 72) s).isNone)
    (x := bridgehubRunF wRegistryCfg (init wRegistryCfg 1) wRegistryRun) (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at hP
  obtain ⟨⟨⟨h1, h2, h3⟩, h4⟩, h5⟩ := hP
  obtain ⟨s', hx, hb⟩ := any_some h4
  simp only [decide_eq_true_eq] at hb
  exact ⟨wRegistryCfg, s, s', 1, 11, 61, 8, 0, 72, reach_of_runF hs, by rw [h1]; decide,
    by rw [h1]; decide, by rw [h2]; decide, by rw [h3]; decide, hx, hb.1, hb.2.1, hb.2.2, h5⟩

/-- `Properties.SettlementLayerOfAChainNeedNotSettleHere`, proved: after `wRegistryRun`
(chain `11` on `10`), the owner whitelists chain `12` and removes `10` from the whitelist,
and the handler migrates `10` onto `12`. -/
theorem SettlementLayerOfAChainNeedNotSettleHere :
    Properties.SettlementLayerOfAChainNeedNotSettleHere := by
  obtain ⟨s, hs, hP⟩ := any_some (p := fun (s : State) => decide (s.settlementLayer 11 = 10 ∧
      s.settlementLayer 10 = 12 ∧ s.whitelistedSL 10 = false))
    (x := bridgehubRunF wRegistryCfg (init wRegistryCfg 1)
      (wRegistryRun ++ [(1, .setSettlementLayerStatus 12 true),
        (1, .setSettlementLayerStatus 10 false), (53, .burnSetSettlementLayer 10 12)]))
    (by decide +kernel)
  simp only [decide_eq_true_eq] at hP
  exact ⟨wRegistryCfg, s, 11, 10, 12, reach_of_runF hs, by decide, by decide, by decide,
    hP.1, hP.2.1, hP.2.2⟩

/-- The two-bridges request used by `WithoutMinAddressCheckLowSender`: second bridge at the
reserved address `1`. -/
private def wRegistryLowRequest : TwoBridgesRequest :=
  { chainId := 10, mintValue := 1, l2Value := 0, refundRecipient := 0,
    secondBridgeAddress := 1, secondBridgeValue := 0 }

/-- `Properties.WithoutMinAddressCheckLowSender`, proved. -/
theorem WithoutMinAddressCheckLowSender : Properties.WithoutMinAddressCheckLowSender := by
  obtain ⟨s, hs, hP⟩ := any_some (p := fun (s : State) =>
      (requestTwoBridgesNoMinAddress wRegistryCfg s 1 ⟨1, 0⟩ wRegistryLowRequest ⟨5, 0⟩).any
        (fun (o : Outcome) => decide (o.l2Sender ≤ minSecondBridgeAddress)) &&
      (requestTwoBridges wRegistryCfg s 1 ⟨1, 0⟩ wRegistryLowRequest ⟨5, 0⟩).isNone)
    (x := bridgehubRunF wRegistryCfg (init wRegistryCfg 1) wRegistryRun) (by decide +kernel)
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hP
  obtain ⟨h1, h2⟩ := hP
  obtain ⟨o, hx, hl⟩ := any_some h1
  exact ⟨wRegistryCfg, s, 1, ⟨1, 0⟩, wRegistryLowRequest, ⟨5, 0⟩, o, reach_of_runF hs, hx,
    by simpa using hl, h2⟩

/-! ## Non-vacuity -/

/-- `Properties.RegistryRunWitness`, proved. -/
theorem RegistryRunWitness : Properties.RegistryRunWitness := by
  have hl : ∀ k ∈ wRegistryRun, k.2.handlerRegistryWrite = false ∧
      k.2.uncheckedRegistration = false ∧ k.2.ctmAssetDisciplined = true := by decide +kernel
  have hf : (wRegistryRun.filter fun k => k.2.registers 10).length = 1 := by decide +kernel
  obtain ⟨s, hs, hP⟩ := any_some (p := fun (s : State) => decide (
      s.chainTypeManager 10 = 60 ∧ s.chainTypeManager 11 = 60 ∧ s.chainTypeManager 12 = 61 ∧
      s.baseTokenAssetId 10 = 7 ∧ s.baseTokenAssetId 11 = 7 ∧ s.baseTokenAssetId 12 = 8 ∧
      s.assetIdRegistered 8 = true ∧ s.zkKeys.card = 3 ∧
      s.ctmAssetIdFromAddress 60 ≠ 0 ∧ s.ctmAssetIdToAddress (s.ctmAssetIdFromAddress 60) = 60 ∧
      s.ctmAssetIdFromAddress 61 ≠ 0 ∧ s.ctmAssetIdToAddress (s.ctmAssetIdFromAddress 61) = 61 ∧
      s.whitelistedSL 10 = true ∧ s.settlementLayer 11 = 10))
    (x := bridgehubRunF wRegistryCfg (init wRegistryCfg 1) wRegistryRun) (by decide +kernel)
  simp only [decide_eq_true_eq] at hP
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hP
  exact ⟨s, (run_iff_runF _ _ _ _).2 hs, hl, hf, h1, h2, h3, h4, h5, h6, by decide, h7, h8, h9,
    h10, h11, h12, wRegistry_no_collision _ _, wRegistry_no_collision _ _, h13, by decide, h14⟩

/-- `Properties.ChainCountLimitWitness`, proved. -/
theorem ChainCountLimitWitness : Properties.ChainCountLimitWitness := by
  have hl : ∀ k ∈ wRegistryRun ++ [((53 : Address), Action.registerNewZKChain 12 82 true)],
      k.2.uncheckedRegistration = false := by decide +kernel
  obtain ⟨s, hs, hP⟩ := any_some (p := fun (s : State) => decide (s.zkKeys.card = 3) &&
      (exec { wRegistryCfg with maxChains := 3 } 53 (.registerNewZKChain 13 73 true) s).isNone &&
      (exec { wRegistryCfg with maxChains := 3 } 1 (.createNewChain 14 60 7 0 74) s).isNone)
    (x := bridgehubRunF { wRegistryCfg with maxChains := 3 }
      (init { wRegistryCfg with maxChains := 3 } 1)
      (wRegistryRun ++ [(53, .registerNewZKChain 12 82 true)])) (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at hP
  exact ⟨s, (run_iff_runF _ _ _ _).2 hs, hl, hP.1.1, hP.1.2, hP.2⟩

/-- `Properties.HandlerRunWitness`, proved. -/
theorem HandlerRunWitness : Properties.HandlerRunWitness := by
  have hl : ∀ k ∈ wRegistryHandlerRun, k.2.burnFor 10 = false ∧ k.2.bridgeMintFor 10 = false ∧
      k.2.bridgeMintFor 12 = false ∧ k.2.handlerRegistersFor 10 = false ∧
      k.2.handlerRegistersFor 11 = false ∧ k.2.registers 10 = false := by decide +kernel
  have he1 : ∃ k ∈ wRegistryHandlerRun, k.2.burnFor 12 = true := by decide +kernel
  have he2 : ∃ k ∈ wRegistryHandlerRun, k.2.bridgeMintFor 11 = true := by decide +kernel
  have he3 : ∃ k ∈ wRegistryHandlerRun, k.2.handlerRegistersFor 12 = true := by decide +kernel
  obtain ⟨s, hs, hP⟩ := any_some (p := fun (s : State) =>
      (bridgehubRunF wRegistryCfg s wRegistryHandlerRun).any fun (t : State) => decide (
        s.chainTypeManager 10 ≠ 0 ∧ s.chainTypeManager 11 = 60 ∧ s.chainTypeManager 12 ≠ 0 ∧
        s.settlementLayer 10 = 1 ∧
        t.chainTypeManager 11 = 61 ∧ s.baseTokenAssetId 11 = 7 ∧ t.baseTokenAssetId 11 = 8 ∧
        getZKChain s 12 = 72 ∧ getZKChain t 12 = 82 ∧ getZKChain t 11 = 71 ∧
        s.zkKeys ⊆ t.zkKeys ∧ (13 : ChainId) ∉ s.zkKeys ∧ (13 : ChainId) ∈ t.zkKeys ∧
        t.chainTypeManager 13 = 0 ∧ getZKChain t 13 = 73 ∧
        s.assetIdRegistered 8 = true ∧ t.assetIdRegistered 8 = true))
    (x := bridgehubRunF wRegistryCfg (init wRegistryCfg 1) wRegistryRun) (by decide +kernel)
  obtain ⟨t, ht, hQ⟩ := any_some hP
  simp only [decide_eq_true_eq] at hQ
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := hQ
  exact ⟨s, t, (run_iff_runF _ _ _ _).2 hs, (run_iff_runF _ _ _ _).2 ht, h1, h2, h3, h4, hl,
    he1, he2, he3, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

/-- `Properties.RegistryStepWitness`, proved. -/
theorem RegistryStepWitness : Properties.RegistryStepWitness := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, hs, hP⟩ := any_some (p := fun (s : State) =>
        (exec wRegistryCfg 1 (.createNewChain 10 60 7 0 70) s).any fun (s' : State) => decide (
          s'.chainTypeManager 10 ≠ s.chainTypeManager 10 ∧
          s'.settlementLayer 10 ≠ s.settlementLayer 10 ∧
          getZKChain s 10 = 0 ∧ getZKChain s' 10 = 70))
      (x := bridgehubRunF wRegistryCfg (init wRegistryCfg 1) wRegistryPrelude)
      (by decide +kernel)
    obtain ⟨s', hx, hQ⟩ := any_some hP
    simp only [decide_eq_true_eq] at hQ
    exact ⟨s, s', (run_iff_runF _ _ _ _).2 hs, hx, fun he => hQ.1 (congrFun he 10),
      fun he => hQ.2.1 (congrFun he 10), hQ.2.2.1, hQ.2.2.2⟩
  · obtain ⟨s, hs, hP⟩ := any_some (p := fun (s : State) =>
        (exec wRegistryCfg 1 (.registerAlreadyDeployed 12 72 ⟨12, 61, 8, 99⟩) s).isSome)
      (x := bridgehubRunF wRegistryCfg (init wRegistryCfg 1)
        (wRegistryPrelude ++ [wRegistryCreate10, (1, .createNewChain 11 60 7 0 71)]))
      (by decide +kernel)
    obtain ⟨s', hx⟩ := Option.isSome_iff_exists.1 hP
    exact ⟨s, s', (run_iff_runF _ _ _ _).2 hs, hx⟩
  · obtain ⟨s, hs, hP⟩ := any_some (p := fun (s : State) =>
        (exec wRegistryCfg 53 (.burnSetSettlementLayer 11 10) s).any fun (s' : State) => decide (
          s.settlementLayer 11 = 1 ∧ s'.settlementLayer 11 = 10))
      (x := bridgehubRunF wRegistryCfg (init wRegistryCfg 1)
        (wRegistryPrelude ++ [wRegistryCreate10] ++ wRegistryRest))
      (by decide +kernel)
    obtain ⟨s', hx, hQ⟩ := any_some hP
    simp only [decide_eq_true_eq] at hQ
    exact ⟨s, s', (run_iff_runF _ _ _ _).2 hs, hx, hQ.1, hQ.2⟩
  · obtain ⟨s, hs, hP⟩ := any_some (p := fun (s : State) =>
        (exec wRegistryCfg 53 (.registerNewZKChain 12 82 true) s).any fun (s' : State) => decide (
          getZKChain s 12 = 72 ∧ getZKChain s' 12 = 82))
      (x := bridgehubRunF wRegistryCfg (init wRegistryCfg 1)
        (wRegistryRun ++ wRegistryHandlerPrefix))
      (by decide +kernel)
    obtain ⟨s', hx, hQ⟩ := any_some hP
    simp only [decide_eq_true_eq] at hQ
    exact ⟨s, s', (run_iff_runF _ _ _ _).2 hs, hx, hQ.1, hQ.2⟩
  · obtain ⟨s, hs, hP⟩ := any_some (p := fun (s : State) =>
        (exec wRegistryCfg 1 (.createNewChain 14 60 7 0 74) s).isSome &&
        (exec wRegistryCfg 1 .pause s).any fun (s' : State) => decide (s'.paused = true))
      (x := bridgehubRunF wRegistryCfg (init wRegistryCfg 1) wRegistryRun)
      (by decide +kernel)
    simp only [Bool.and_eq_true] at hP
    obtain ⟨h1, h2⟩ := hP
    obtain ⟨s', hx, hQ⟩ := any_some h2
    exact ⟨s, s', (run_iff_runF _ _ _ _).2 hs, h1, hx, by simpa using hQ⟩

/-- `Properties.RequestWitness`, proved. -/
theorem RequestWitness : Properties.RequestWitness := by
  have hl : ∀ k ∈ wRegistryRest ++ [wRegistryBurn11] ++ wRegistryHandlerRun,
      k.2.bridgeMintFor 10 = false ∧ k.2.handlerRegistersFor 10 = false := by decide +kernel
  obtain ⟨s, hs, hP⟩ := any_some (p := fun (s : State) =>
      (requestDirect wRegistryCfg s 1 ⟨3, 0⟩
        { chainId := 10, mintValue := 3, l2Contract := 0, l2Value := 0,
          refundRecipient := 0 }).any (fun (o : Outcome) => decide (o.ethToAssetRouter = 3)) &&
      (requestDirect wRegistryCfg s 1 ⟨0, 0⟩
        { chainId := 12, mintValue := 3, l2Contract := 0, l2Value := 0,
          refundRecipient := 0 }).any
        (fun (o : Outcome) => decide (o.depositAssetId = 8 ∧ o.ethToAssetRouter = 0)) &&
      (requestTwoBridges wRegistryCfg s 1 ⟨5, 0⟩
        { chainId := 10, mintValue := 3, l2Value := 0, refundRecipient := 0,
          secondBridgeAddress := 70000, secondBridgeValue := 2 } ⟨5, 0⟩).any
        (fun (o : Outcome) => decide (o.ethToAssetRouter = 3 ∧ o.ethToSecondBridge = 2)) &&
      (requestTwoBridges wRegistryCfg s 1 ⟨2, 0⟩
        { chainId := 12, mintValue := 3, l2Value := 0, refundRecipient := 0,
          secondBridgeAddress := 70000, secondBridgeValue := 2 } ⟨5, 0⟩).any
        (fun (o : Outcome) => decide (o.depositAssetId = 8 ∧ o.ethToAssetRouter = 0 ∧
          o.ethToSecondBridge = 2)))
    (x := bridgehubRunF wRegistryCfg (init wRegistryCfg 1) wRegistryRun) (by decide +kernel)
  obtain ⟨t, ht, hQ⟩ := any_some (p := fun (t : State) =>
      (requestDirect wRegistryCfg t 1 ⟨3, 0⟩
        { chainId := 10, mintValue := 3, l2Contract := 0, l2Value := 0,
          refundRecipient := 0 }).any (fun (o : Outcome) => decide (o.depositAssetId = 7 ∧ o.target = 70)) &&
      (requestDirect wRegistryCfg t 1 ⟨0, 0⟩
        { chainId := 13, mintValue := 0, l2Contract := 0, l2Value := 0,
          refundRecipient := 0 }).any (fun (o : Outcome) => decide ((13 : ChainId) ∈ t.zkKeys ∧
            t.chainTypeManager 13 = 0 ∧ o.target = 73)))
    (x := bridgehubRunF wRegistryCfg (init wRegistryCfg 1) (wRegistryPrelude ++
      [wRegistryCreate10] ++ (wRegistryRest ++ [wRegistryBurn11] ++ wRegistryHandlerRun)))
    (by decide +kernel)
  simp only [Bool.and_eq_true] at hP hQ
  obtain ⟨⟨⟨p1, p2⟩, p3⟩, p4⟩ := hP
  obtain ⟨q1, q2⟩ := hQ
  obtain ⟨o1, e1, r1⟩ := any_some p1
  obtain ⟨o2, e2, r2⟩ := any_some p2
  obtain ⟨o3, e3, r3⟩ := any_some p3
  obtain ⟨o4, e4, r4⟩ := any_some p4
  obtain ⟨o5, e5, r5⟩ := any_some q1
  obtain ⟨o6, e6, r6⟩ := any_some q2
  simp only [decide_eq_true_eq] at r1 r2 r3 r4 r5 r6
  exact ⟨s, t, (run_iff_runF _ _ _ _).2 hs, (run_iff_runF _ _ _ _).2 ht, hl,
    ⟨o1, e1, r1⟩, ⟨o2, e2, r2⟩, ⟨o3, e3, r3⟩, ⟨o4, e4, r4⟩, ⟨o5, e5, r5⟩, ⟨o6, e6, r6⟩⟩

end Contracts.Bridgehub
