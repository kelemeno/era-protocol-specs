import EraSpec.Contracts.Bridgehub.Properties.Registry

/-!
# Proofs: `L1Bridgehub`

Proofs of `EraSpec.Contracts.Bridgehub.Properties.Registry`.

The run-level results are inductions over `Run`. Each one-step lemma does a case split
over all 22 entry points and over every guard, so a new entry point or a changed guard
breaks the proof rather than slipping past it. Runs are also computed by `runF`, which
makes splitting a run at a call (`run_append_iff`) a list induction.

The countermodels and witnesses are explicit runs from `init`, with small concrete
parameters, checked by evaluation.
-/

namespace Contracts.Bridgehub

/-! ## Runs as a function -/

/-- The run of `l` from `s`, as a function. -/
def runF (cfg : Config) : State → List Call → Option State
  | s, [] => some s
  | s, k :: l => (exec cfg k.1 k.2 s).bind fun u => runF cfg u l

lemma runF_append (cfg : Config) (s : State) (l₁ l₂ : List Call) :
    runF cfg s (l₁ ++ l₂) = (runF cfg s l₁).bind fun u => runF cfg u l₂ := by
  induction l₁ generalizing s with
  | nil => simp [runF]
  | cons k l ih =>
    simp only [List.cons_append, runF]
    cases exec cfg k.1 k.2 s with
    | none => simp
    | some u => simp [ih]

lemma run_iff_runF (cfg : Config) (s t : State) (l : List Call) :
    Run cfg s l t ↔ runF cfg s l = some t := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | snoc k _ hx ih => simp [runF_append, ih, runF, hx]
  · induction l using List.reverseRecOn generalizing t with
    | nil => intro h; simp [runF] at h; subst h; exact Run.nil _
    | append_singleton l k ih =>
      intro h
      rw [runF_append] at h
      cases hl : runF cfg s l with
      | none => simp [hl] at h
      | some u =>
        simp only [hl, Option.bind_some, runF] at h
        cases hx : exec cfg k.1 k.2 u with
        | none => simp [hx] at h
        | some v =>
          simp [hx] at h; subst h
          exact Run.snoc k (ih u hl) hx

lemma run_append_iff (cfg : Config) (s t : State) (l₁ l₂ : List Call) :
    Run cfg s (l₁ ++ l₂) t ↔ ∃ u, Run cfg s l₁ u ∧ Run cfg u l₂ t := by
  simp only [run_iff_runF, runF_append]
  cases runF cfg s l₁ <;> simp

lemma run_single (cfg : Config) (s t : State) (k : Call) :
    Run cfg s [k] t ↔ exec cfg k.1 k.2 s = some t := by
  simp only [run_iff_runF, runF]
  cases exec cfg k.1 k.2 s <;> simp

/-- A state predicate preserved by every successful call holds at the end of every run. -/
lemma Run.invariant {cfg : Config} (P : State → Prop)
    (hstep : ∀ caller a s s', P s → exec cfg caller a s = some s' → P s')
    {s t : State} {l : List Call} (h : Run cfg s l t) (hs : P s) : P t := by
  induction h with
  | nil => exact hs
  | snoc k _ hx ih => exact hstep _ _ _ _ ih hx

/-- The same, for a predicate that holds only along runs whose calls satisfy `Q`. -/
lemma Run.invariantOn {cfg : Config} (Q : Call → Prop) (P : State → Prop)
    (hstep : ∀ caller a s s', Q (caller, a) → P s → exec cfg caller a s = some s' → P s')
    {s t : State} {l : List Call} (h : Run cfg s l t) (hq : ∀ k ∈ l, Q k) (hs : P s) : P t := by
  induction h with
  | nil => exact hs
  | snoc k _ hx ih =>
    exact hstep _ _ _ _ (hq k (by simp)) (ih fun k hk => hq k (by simp [hk])) hx

/-! ## Unfolding a successful call -/

lemma registerNew_eq {cfg : Config} {s s' : State} {c : ChainId} {z : Address} {chk : Bool} :
    registerNew cfg s c z chk = some s' ↔
      ¬ (chk = true ∧ (insert c s.zkKeys).card > cfg.maxChains) ∧
      s' = { s with zkKeys := insert c s.zkKeys, zkAddr := Function.update s.zkAddr c z } := by
  unfold registerNew
  split_ifs with h <;> simp_all [eq_comm]

lemma map_const_eq {α : Type} {o : Option α} {s s' : State} :
    o.map (fun _ => s) = some s' ↔ o.isSome ∧ s' = s := by
  cases o <;> simp [eq_comm]

/-- Normalise `exec … = some s'` for one entry point: split every guard, and substitute
the post-state. -/
macro "exec_unfold" h:ident : tactic => `(tactic| (
  simp only [exec, map_const_eq, writeChain] at $h:ident
  try split_ifs at $h:ident
  all_goals (try simp only [registerNew_eq] at $h:ident)
  all_goals (try (obtain ⟨_, hh⟩ := $h:ident; subst hh))
  all_goals (try (cases $h:ident))))

/-- Close a goal about a post-state: split the point updates, then simplify. -/
macro "upd_close" : tactic => `(tactic| (
  try simp only [Function.update_apply] at *
  try split_ifs at *
  all_goals (try subst_vars)
  all_goals simp_all [ValidChainParams]))


/-! ## Chain registration -/

lemma step_ctm_ne {cfg : Config} {caller : Address} {a : Action} {s s' : State} {c : ChainId}
    (h : exec cfg caller a s = some s') (hc : s.chainTypeManager c ≠ 0) :
    s'.chainTypeManager c ≠ 0 := by
  cases a <;> exec_unfold h <;> upd_close

lemma step_registers {cfg : Config} {caller : Address} {a : Action} {s s' : State} {c : ChainId}
    (h : exec cfg caller a s = some s') (hr : a.registers c = true) :
    s.chainTypeManager c = 0 ∧ s'.chainTypeManager c ≠ 0 := by
  cases a <;> simp only [Action.registers, decide_eq_true_eq, Bool.false_eq_true] at hr <;>
    subst hr <;> exec_unfold h <;> upd_close

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

lemma init_ctm (cfg : Config) (o : Address) (c : ChainId) : (init cfg o).chainTypeManager c = 0 := rfl

lemma step_baseRegistered {cfg : Config} {caller : Address} {a : Action} {s s' : State}
    (h : exec cfg caller a s = some s')
    (hp : ∀ c, s.chainTypeManager c ≠ 0 → s.assetIdRegistered (s.baseTokenAssetId c) = true) :
    ∀ c, s'.chainTypeManager c ≠ 0 → s'.assetIdRegistered (s'.baseTokenAssetId c) = true := by
  intro c
  cases a <;> exec_unfold h <;> upd_close

/-- `Properties.ChainBaseTokenRegistered`, proved. -/
theorem ChainBaseTokenRegistered : Properties.ChainBaseTokenRegistered := by
  rintro cfg s ⟨o, l, h⟩
  exact Run.invariant (fun u => ∀ c, u.chainTypeManager c ≠ 0 →
      u.assetIdRegistered (u.baseTokenAssetId c) = true)
    (fun _ _ _ _ hp hx => step_baseRegistered hx hp) h (fun c hc => absurd rfl hc)

lemma step_approved {cfg : Config} {caller : Address} {a : Action} {s s' : State}
    (A : Address → Prop) (h : exec cfg caller a s = some s')
    (h1 : ∀ m, s.ctmRegistered m = true → A m)
    (h2 : ∀ id, s.ctmAssetIdToAddress id ≠ 0 → A (s.ctmAssetIdToAddress id))
    (h3 : ∀ c, s.chainTypeManager c ≠ 0 → A (s.chainTypeManager c))
    (hadd : ∀ m, a = .addChainTypeManager m → A m) :
    (∀ m, s'.ctmRegistered m = true → A m) ∧
    (∀ id, s'.ctmAssetIdToAddress id ≠ 0 → A (s'.ctmAssetIdToAddress id)) ∧
    (∀ c, s'.chainTypeManager c ≠ 0 → A (s'.chainTypeManager c)) := by
  cases a <;> exec_unfold h <;>
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩ <;> upd_close

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

lemma step_fixed {cfg : Config} {caller : Address} {a : Action} {s s' : State} {c : ChainId}
    (h : exec cfg caller a s = some s') (hm : a.bridgeMintFor c = false)
    (hc : s.chainTypeManager c ≠ 0) :
    s'.chainTypeManager c = s.chainTypeManager c ∧ s'.baseTokenAssetId c = s.baseTokenAssetId c := by
  cases a <;> simp only [Action.bridgeMintFor, decide_eq_false_iff_not] at hm <;>
    exec_unfold h <;> upd_close

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

lemma step_consistent {cfg : Config} {caller : Address} {a : Action} {s s' : State}
    (h : exec cfg caller a s = some s') (hq : a.handlerRegistryWrite = false)
    (hp : ∀ c, (c ∈ s.zkKeys ↔ s.chainTypeManager c ≠ 0) ∧ (c ∈ s.zkKeys ↔ s.zkAddr c ≠ 0)) :
    ∀ c, (c ∈ s'.zkKeys ↔ s'.chainTypeManager c ≠ 0) ∧ (c ∈ s'.zkKeys ↔ s'.zkAddr c ≠ 0) := by
  intro c
  have hc := hp c
  cases a <;> simp only [Action.handlerRegistryWrite, Bool.true_eq_false] at hq <;>
    exec_unfold h <;> upd_close

/-- `Properties.RegistryConsistentWithoutHandler`, proved. -/
theorem RegistryConsistentWithoutHandler : Properties.RegistryConsistentWithoutHandler := by
  intro cfg o l s h hl
  exact Run.invariantOn (fun k => k.2.handlerRegistryWrite = false)
    (fun u => ∀ c, (c ∈ u.zkKeys ↔ u.chainTypeManager c ≠ 0) ∧ (c ∈ u.zkKeys ↔ u.zkAddr c ≠ 0))
    (fun _ _ _ _ hq hp hx => step_consistent hx hq hp) h hl (fun c => by simp [init])

lemma step_card {cfg : Config} {caller : Address} {a : Action} {s s' : State}
    (h : exec cfg caller a s = some s') (hq : a.uncheckedRegistration = false)
    (hp : s.zkKeys.card ≤ cfg.maxChains) : s'.zkKeys.card ≤ cfg.maxChains := by
  cases a <;> simp only [Action.uncheckedRegistration, Bool.not_eq_false'] at hq <;>
    exec_unfold h <;> simp_all

/-- `Properties.ChainCountBounded`, proved. -/
theorem ChainCountBounded : Properties.ChainCountBounded := by
  intro cfg o l s h hl
  exact Run.invariantOn (fun k => k.2.uncheckedRegistration = false)
    (fun u => u.zkKeys.card ≤ cfg.maxChains)
    (fun _ _ _ _ hq hp hx => step_card hx hq hp) h hl (by simp [init])

/-- The round-trip invariant: every set `ctmAssetIdFromAddress[m]` is an encoding of `m`,
and it round-trips unless that encoding collides with another CTM's. -/
def RoundTripInv (cfg : Config) (s : State) : Prop :=
  ∀ m, s.ctmAssetIdFromAddress m ≠ 0 →
    (∃ dep, s.ctmAssetIdFromAddress m = cfg.encodeAssetId cfg.thisChain m dep) ∧
    (s.ctmAssetIdToAddress (s.ctmAssetIdFromAddress m) = m ∨
      ∃ m' dep dep', m' ≠ m ∧
        cfg.encodeAssetId cfg.thisChain m dep = cfg.encodeAssetId cfg.thisChain m' dep')

lemma step_roundTrip {cfg : Config} {caller : Address} {a : Action} {s s' : State}
    (h : exec cfg caller a s = some s') (hq : a.ctmAssetDisciplined = true)
    (hp : RoundTripInv cfg s) : RoundTripInv cfg s' := by
  cases a with
  | setCTMAssetAddress d m₀ =>
    simp only [Action.ctmAssetDisciplined, decide_eq_true_eq] at hq
    subst hq
    exec_unfold h
    intro m hm
    simp only [Function.update_apply] at hm ⊢
    by_cases hmm : m = d
    · subst hmm; simp
    · simp only [hmm, ite_false] at hm ⊢
      obtain ⟨⟨dep, hdep⟩, hrt⟩ := hp m hm
      refine ⟨⟨dep, hdep⟩, ?_⟩
      by_cases hid : s.ctmAssetIdFromAddress m = cfg.encodeAssetId cfg.thisChain d caller
      · exact Or.inr ⟨d, dep, caller, Ne.symm hmm, hdep.symm.trans hid⟩
      · simpa [hid] using hrt
  | _ => exec_unfold h <;> exact hp

/-- `Properties.CtmAssetIdRoundTrip`, proved. -/
theorem CtmAssetIdRoundTrip : Properties.CtmAssetIdRoundTrip := by
  intro cfg o l s h hl m hm
  exact (Run.invariantOn (fun k => k.2.ctmAssetDisciplined = true) (RoundTripInv cfg)
    (fun _ _ _ _ hq hp hx => step_roundTrip hx hq hp) h hl
    (fun m hm => absurd rfl hm) m hm).2

lemma step_whitelisted {cfg : Config} {caller : Address} {a : Action} {s s' : State}
    (h : exec cfg caller a s = some s')
    (hp : ∀ c, s.whitelistedSL c = true → c = cfg.thisChain ∨ s.settlementLayer c = cfg.thisChain) :
    ∀ c, s'.whitelistedSL c = true → c = cfg.thisChain ∨ s'.settlementLayer c = cfg.thisChain := by
  intro c hc
  have hpc := hp c
  cases a <;> exec_unfold h <;> upd_close

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
  cases a <;> exec_unfold h <;> upd_close

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

lemma request_facts {cfg : Config} {s : State} {caller : Address} {env : CallEnv} {o : Outcome}
    {c : ChainId}
    (h : (∃ req : DirectRequest, req.chainId = c ∧ requestDirect cfg s caller env req = some o) ∨
       (∃ (req : TwoBridgesRequest) (reply : SecondBridgeReply), req.chainId = c ∧
          requestTwoBridges cfg s caller env req reply = some o)) :
    ZkGetOk s c ∧ o.target = s.zkAddr c ∧ o.depositAssetId = s.baseTokenAssetId c := by
  rcases h with ⟨req, rfl, h⟩ | ⟨req, reply, rfl, h⟩
  · obtain ⟨-, h1, -, h2, -, -, -, -, h3, -⟩ := DirectRequestAccounting cfg s caller env req o h
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
  refine ⟨hc1.1 hkey, ht ▸ hc2.1 hkey, by simp [ht, getZKChain, hkey], ?_⟩
  rw [hd]
  exact ChainBaseTokenRegistered cfg s ⟨o, l, h⟩ c (hc1.1 hkey)

lemma exec_create {cfg : Config} {caller : Address} {c : ChainId} {m : Address} {a : AssetId}
    {adm d : Address} {s s' : State}
    (h : exec cfg caller (.createNewChain c m a adm d) s = some s') :
    s'.chainTypeManager c = m ∧ m ≠ 0 ∧ s'.baseTokenAssetId c = a ∧ c ∈ s'.zkKeys ∧
      s'.zkAddr c = d := by
  exec_unfold h; simp_all [ValidChainParams]

lemma step_zk_fixed {cfg : Config} {caller : Address} {a : Action} {s s' : State} {c : ChainId}
    (h : exec cfg caller a s = some s') (hq : a.handlerRegistryWrite = false)
    (hk : c ∈ s.zkKeys) (hc : s.chainTypeManager c ≠ 0) :
    c ∈ s'.zkKeys ∧ s'.zkAddr c = s.zkAddr c := by
  cases a <;> simp only [Action.handlerRegistryWrite, Bool.true_eq_false] at hq <;>
    exec_unfold h <;> upd_close

/-- `Properties.RequestChargesCreationBaseToken`, proved. -/
theorem RequestChargesCreationBaseToken : Properties.RequestChargesCreationBaseToken := by
  intro cfg s t l₁ l₂ caller₀ c m a adm d h hl₂ caller env o hreq
  obtain ⟨v, hv, h2⟩ := (run_append_iff cfg s t _ l₂).1 h
  obtain ⟨u, -, hk⟩ := (run_append_iff cfg s v l₁ _).1 hv
  obtain ⟨hm, hm0, ha, hkey, hd⟩ := exec_create ((run_single cfg u v _).1 hk)
  obtain ⟨-, ht, hdep⟩ := request_facts hreq
  have hfix := CtmAndBaseTokenFixedOutsideBridgeMint cfg v t l₂ h2 c hl₂ (hm ▸ hm0)
  refine ⟨by rw [hdep, hfix.2, ha], fun hl => ?_⟩
  have := Run.invariantOn (fun k => k.2.handlerRegistryWrite = false)
    (fun w => c ∈ w.zkKeys ∧ w.zkAddr c = d ∧ w.chainTypeManager c ≠ 0)
    (fun _ _ _ _ hq hp hx => by
      obtain ⟨e1, e2⟩ := step_zk_fixed hx hq hp.1 hp.2.2
      exact ⟨e1, e2.trans hp.2.1, step_ctm_ne hx hp.2.2⟩) h2 hl ⟨hkey, hd, hm ▸ hm0⟩
  rw [ht, this.2.1]

/-! ## Authority and pause -/

/-- `Properties.RegistryWritesAuthorized`, proved. -/
theorem RegistryWritesAuthorized : Properties.RegistryWritesAuthorized := by
  intro cfg caller a s s' h
  cases a <;> exec_unfold h <;> simp_all <;> tauto

/-- `Properties.PauseBlocksCreationAndRequests`, proved. -/
theorem PauseBlocksCreationAndRequests : Properties.PauseBlocksCreationAndRequests := by
  intro cfg s hp caller
  exact ⟨fun _ _ _ _ _ => by simp [exec, hp], fun _ _ => by simp [requestDirect, hp],
    fun _ _ _ => by simp [requestTwoBridges, hp]⟩

/-! ## Countermodels and witnesses

All use one concrete deployment, `wcfg`, and runs from `init wcfg 1` (owner `1`). The
asset-id hash is `fun _ d _ => d + 100`, injective in the data argument. Addresses:
asset router `50`, CTM deployer `51`, message root `52`, chain asset handler `53`,
registration sender `54`, CTM `60` (and `61`). ETH's asset id is `7`. -/

/-- The concrete deployment used by the countermodels and witnesses. -/
def wcfg : Config where
  thisChain := 1
  self := 99
  ethAssetId := 7
  maxChains := 10
  upgrader := 98
  twoBridgesMagic := 5
  encodeAssetId := fun _ d _ => d + 100

lemma reach_of_runF {cfg : Config} {o : Address} {l : List Call} {s : State}
    (h : runF cfg (init cfg o) l = some s) : Reachable cfg s :=
  ⟨o, l, (run_iff_runF _ _ _ _).2 h⟩

lemma witness_of {cfg : Config} {o : Address} {l : List Call} {P : State → Bool}
    (h : (runF cfg (init cfg o) l).any P = true) : ∃ s, Reachable cfg s ∧ P s = true := by
  cases hr : runF cfg (init cfg o) l with
  | none => simp [hr] at h
  | some s => exact ⟨s, reach_of_runF hr, by simpa [hr] using h⟩

lemma any_some {α : Type} {p : α → Bool} {x : Option α} (h : x.any p = true) :
    ∃ a, x = some a ∧ p a = true := by
  cases x <;> simp_all

/-- Set the addresses, add CTM `60`, create chains `10` and `11` (ETH-based, diamonds
`70` and `71`). -/
def wSetup : List Call :=
  [(1, .setAddresses 50 51 52 53 54), (1, .addChainTypeManager 60),
   (1, .createNewChain 10 60 7 0 70), (1, .createNewChain 11 60 7 0 71)]

/-- `wSetup`, then whitelist chain `10` and migrate chain `11` onto it. -/
def wMigrated : List Call :=
  wSetup ++ [(1, .setSettlementLayerStatus 10 true), (53, .burnSetSettlementLayer 11 10)]

/-- `Properties.RegistrationWitness`, proved. -/
theorem RegistrationWitness : Properties.RegistrationWitness := by
  obtain ⟨s, hs, hP⟩ := witness_of (cfg := wcfg) (o := 1) (l := wMigrated)
    (P := fun s => decide (s.chainTypeManager 10 ≠ 0 ∧ s.chainTypeManager 11 ≠ 0 ∧
      s.whitelistedSL 10 = true ∧ s.settlementLayer 11 = 10 ∧ s.zkKeys.card = 2))
    (by decide +kernel)
  simp only [decide_eq_true_eq] at hP
  exact ⟨wcfg, s, 10, 11, hs, by decide, by decide, hP.1, hP.2.1, hP.2.2.1, hP.2.2.2.1,
    hP.2.2.2.2⟩

/-- `Properties.BridgeMintRewritesBaseToken`, proved. -/
theorem BridgeMintRewritesBaseToken : Properties.BridgeMintRewritesBaseToken := by
  obtain ⟨s, hs, hP⟩ := witness_of (cfg := wcfg) (o := 1)
    (l := wMigrated ++ [(51, .setCTMAssetAddress 60 60)])
    (P := fun s => decide (s.chainTypeManager 11 ≠ 0 ∧ s.baseTokenAssetId 11 = 7) &&
      (exec wcfg 53 (.forwardedBridgeMint 160 11 8) s).any
        (fun (s' : State) => decide (s'.baseTokenAssetId 11 = 8)))
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
  obtain ⟨⟨h1, h2⟩, h3⟩ := hP
  obtain ⟨s', hx, hb⟩ := any_some h3
  exact ⟨wcfg, s, s', 53, 160, 11, 8, hs, h1, by rw [h2]; decide, hx, by simpa using hb⟩

/-- `Properties.HandlerEntryOverwrittenByCreate`, proved. -/
theorem HandlerEntryOverwrittenByCreate : Properties.HandlerEntryOverwrittenByCreate := by
  obtain ⟨s, hs, hP⟩ := witness_of (cfg := wcfg) (o := 1)
    (l := [(1, .setAddresses 50 51 52 53 54), (1, .addChainTypeManager 60),
      (53, .registerNewZKChain 11 80 true)])
    (P := fun s => decide ((11 : ChainId) ∈ s.zkKeys ∧ s.chainTypeManager 11 = 0 ∧
        s.zkAddr 11 = 80) &&
      (exec wcfg 1 (.createNewChain 11 60 7 0 71) s).any (fun (s' : State) => decide (s'.zkAddr 11 = 71)))
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hP
  obtain ⟨s', hx, hz⟩ := any_some h4
  exact ⟨wcfg, s, s', 1, 11, 60, 7, 0, 71, hs, h1, h2, by rw [h3]; decide, hx,
    by simpa using hz, by rw [h3]; decide⟩

/-- `Properties.CtmAssetIdRoundTripNeedsDiscipline`, proved. -/
theorem CtmAssetIdRoundTripNeedsDiscipline : Properties.CtmAssetIdRoundTripNeedsDiscipline := by
  obtain ⟨s, hs, hP⟩ := witness_of (cfg := wcfg) (o := 1)
    (l := [(1, .setAddresses 50 51 52 53 54), (1, .addChainTypeManager 60),
      (1, .addChainTypeManager 61), (51, .setCTMAssetAddress 5 60),
      (51, .setCTMAssetAddress 5 61)])
    (P := fun s => decide (s.ctmAssetIdFromAddress 60 ≠ 0 ∧
      s.ctmAssetIdToAddress (s.ctmAssetIdFromAddress 60) ≠ 60))
    (by decide +kernel)
  simp only [decide_eq_true_eq] at hP
  exact ⟨wcfg, s, 60, fun x y d d' h => add_right_cancel h, hs, hP.1, hP.2⟩

/-- `Properties.WithoutCheckWhitelistedLayerLeaves`, proved. -/
theorem WithoutCheckWhitelistedLayerLeaves : Properties.WithoutCheckWhitelistedLayerLeaves := by
  obtain ⟨s, hs, hP⟩ := witness_of (cfg := wcfg) (o := 1)
    (l := wSetup ++ [(1, .setSettlementLayerStatus 10 true),
      (1, .setSettlementLayerStatus 11 true)])
    (P := fun s => (burnNoSettlementLayerCheck wcfg 53 s 10 11).any
      (fun (s' : State) => decide (s'.whitelistedSL 10 = true ∧ s'.settlementLayer 10 ≠ 1)))
    (by decide +kernel)
  obtain ⟨s', hx, hb⟩ := any_some hP
  simp only [decide_eq_true_eq] at hb
  exact ⟨wcfg, s, s', 53, 10, 11, hs, hx, hb.1, by decide, hb.2⟩

/-- `Properties.RemovedCtmStillAssignedByBridgeMint`, proved. -/
theorem RemovedCtmStillAssignedByBridgeMint : Properties.RemovedCtmStillAssignedByBridgeMint := by
  obtain ⟨s, hs, hP⟩ := witness_of (cfg := wcfg) (o := 1)
    (l := [(1, .setAddresses 50 51 52 53 54), (1, .addChainTypeManager 60),
      (51, .setCTMAssetAddress 60 60), (1, .removeChainTypeManager 60)])
    (P := fun s => decide (s.ctmRegistered 60 = false ∧ s.chainTypeManager 11 = 0) &&
      (exec wcfg 53 (.forwardedBridgeMint 160 11 7) s).any
        (fun (s' : State) => decide (s'.chainTypeManager 11 = 60)))
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
  obtain ⟨⟨h1, h2⟩, h3⟩ := hP
  obtain ⟨s', hx, hc⟩ := any_some h3
  exact ⟨wcfg, s, s', 53, 160, 11, 7, 60, hs, h1, h2, hx, by simpa using hc, by decide⟩

/-- The two-bridges request used by `WithoutMinAddressCheckLowSender`: second bridge at the
reserved address `1`. -/
def wLowRequest : TwoBridgesRequest :=
  { chainId := 10, mintValue := 1, l2Value := 0, refundRecipient := 0,
    secondBridgeAddress := 1, secondBridgeValue := 0 }

/-- `Properties.WithoutMinAddressCheckLowSender`, proved. -/
theorem WithoutMinAddressCheckLowSender : Properties.WithoutMinAddressCheckLowSender := by
  obtain ⟨s, hs, hP⟩ := witness_of (cfg := wcfg) (o := 1) (l := wSetup)
    (P := fun s =>
      (requestTwoBridgesNoMinAddress wcfg s 1 ⟨1, 0⟩ wLowRequest ⟨5, 0⟩).any
        (fun (o : Outcome) => decide (o.l2Sender ≤ minSecondBridgeAddress)) &&
      (requestTwoBridges wcfg s 1 ⟨1, 0⟩ wLowRequest ⟨5, 0⟩).isNone)
    (by decide +kernel)
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hP
  obtain ⟨h1, h2⟩ := hP
  obtain ⟨o, hx, hl⟩ := any_some h1
  exact ⟨wcfg, s, 1, ⟨1, 0⟩, wLowRequest, ⟨5, 0⟩, o, hs, hx, by simpa using hl, h2⟩

/-- `Properties.RequestWitness`, proved. -/
theorem RequestWitness : Properties.RequestWitness := by
  let r₁ : DirectRequest :=
    { chainId := 10, mintValue := 3, l2Contract := 0, l2Value := 0, refundRecipient := 0 }
  let r₂ : TwoBridgesRequest :=
    { chainId := 10, mintValue := 3, l2Value := 0, refundRecipient := 0,
      secondBridgeAddress := 70000, secondBridgeValue := 2 }
  obtain ⟨s, hs, hP⟩ := witness_of (cfg := wcfg) (o := 1) (l := wSetup)
    (P := fun s => decide (s.baseTokenAssetId 10 = 7) &&
      (requestDirect wcfg s 1 ⟨3, 0⟩ r₁).any (fun (o : Outcome) => decide (0 < o.ethToAssetRouter)) &&
      (requestTwoBridges wcfg s 1 ⟨5, 0⟩ r₂ ⟨5, 0⟩).any
        (fun (o : Outcome) => decide (0 < o.ethToAssetRouter ∧ 0 < o.ethToSecondBridge)))
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
  obtain ⟨⟨h0, h1⟩, h2⟩ := hP
  obtain ⟨o₁, hx₁, ho₁⟩ := any_some h1
  obtain ⟨o₂, hx₂, ho₂⟩ := any_some h2
  simp only [decide_eq_true_eq] at ho₁ ho₂
  exact ⟨wcfg, s, 1, ⟨3, 0⟩, ⟨5, 0⟩, r₁, r₂, ⟨5, 0⟩, o₁, o₂, hs, h0, hx₁, ho₁, hx₂, ho₂.1, ho₂.2⟩

end Contracts.Bridgehub
