import EraSpec.Contracts.L1Nullifier.Properties.Model

/-!
# Proofs: the nullifier's deposit ledger

Every run-level result is an induction over `Reach` with a one-step lemma that does a case split
over all fifteen `Step` constructors. The ledger results rest on two one-step facts: a write needs
an empty slot (`DepositExists`) and a clear needs the slot to equal the claimed hash
(`DepositDoesNotExist`). The persistence results split a run at the step that logged a given event
(`reach_split`; each step logs at most one event) and apply `RecordLeavesOnlyByPreimage` to the
rest. The countermodels and witnesses are concrete runs from fresh storage.
-/

namespace Contracts.L1Nullifier

/-! ## Slots -/

@[simp] private lemma setSlot_same (m : ChainId → Bytes32 → Bytes32) (c : ChainId) (h v : Bytes32) :
    setSlot m c h v c h = v := by simp [setSlot]

private lemma setSlot_other (m : ChainId → Bytes32 → Bytes32) {c c' : ChainId} {h h' : Bytes32}
    (v : Bytes32) (hk : ¬ (c' = c ∧ h' = h)) : setSlot m c' h' v c h = m c h := by
  simp only [setSlot]
  rw [ite_eq_right]
  rintro ⟨rfl, rfl⟩
  exact hk ⟨rfl, rfl⟩

/-- What one source step does to one slot: nothing; or it writes an empty slot; or it is a clear
of that key whose triple hashes to the slot's old value. -/
private lemma step_slot {env : Env} {cfg : Cfg} {s s' : Sys} {l : Label}
    (hs : Step Checks.source env cfg s l s') (c : ChainId) (h : Bytes32) :
    s'.n.depositHappened c h = s.n.depositHappened c h ∨ s.n.depositHappened c h = 0 ∨
      ∃ cl, s'.log = s.log ++ [.clear cl s.n.l1AssetRouter] ∧ cl.chainId = c ∧ cl.l2TxHash = h ∧
        env.txDataHash cl.triple = s.n.depositHappened c h := by
  have hw : ∀ (o : Origin) (c' : ChainId) (h' v : Bytes32), s.n.depositHappened c' h' = 0 →
      (afterWrite s o c' h' v).n.depositHappened c h = s.n.depositHappened c h ∨
        s.n.depositHappened c h = 0 := by
    intro o c' h' v h0
    by_cases hk : c' = c ∧ h' = h
    · obtain ⟨rfl, rfl⟩ := hk; exact Or.inr h0
    · exact Or.inl (setSlot_other _ _ hk)
  have hc : ∀ cl : Claim,
      s.n.depositHappened cl.chainId cl.l2TxHash = env.txDataHash cl.triple →
      (afterClaim s cl).n.depositHappened c h = s.n.depositHappened c h ∨
        s.n.depositHappened c h = 0 ∨
        ∃ cl', (afterClaim s cl).log = s.log ++ [.clear cl' s.n.l1AssetRouter] ∧
          cl'.chainId = c ∧ cl'.l2TxHash = h ∧
          env.txDataHash cl'.triple = s.n.depositHappened c h := by
    intro cl hd
    by_cases hk : cl.chainId = c ∧ cl.l2TxHash = h
    · obtain ⟨rfl, rfl⟩ := hk
      exact Or.inr (Or.inr ⟨cl, rfl, rfl, rfl, hd.symm⟩)
    · exact Or.inl (setSlot_other _ _ hk)
  cases hs with
  | forwarded _ _ _ hex => exact (hw _ _ _ _ (hex rfl)).imp_right Or.inl
  | twoBridges _ _ _ hex => exact (hw _ _ _ _ (hex rfl)).imp_right Or.inl
  | confirm _ hok => exact hc _ (hok.dataHash rfl)
  | recover _ hok => exact hc _ (hok.dataHash rfl)
  | _ => exact Or.inl rfl

/-! ## The ledger identity -/

private lemma write_count (env : Env) (s : Sys) (o : Origin) (c' : ChainId) (h' v : Bytes32)
    (h0 : s.n.depositHappened c' h' = 0) (c : ChainId) (h : Bytes32) :
    [Event.write o c' h' v].countP (isClear c h) + occupied (afterWrite s o c' h' v).n c h =
      [Event.write o c' h' v].countP (isNzWrite c h) +
        [Event.write o c' h' v].countP (isZeroClear env c h) + occupied s.n c h := by
  by_cases hk : c' = c ∧ h' = h
  · obtain ⟨rfl, rfl⟩ := hk
    by_cases hv : v = 0 <;> simp [afterWrite, occupied, isClear, isNzWrite, isZeroClear, h0, hv]
  · have hk' : ¬ (c' = c ∧ h' = h ∧ v ≠ 0) := fun ⟨a, b, _⟩ => hk ⟨a, b⟩
    simp only [afterWrite, occupied, setSlot_other _ _ hk]
    simp [isClear, isNzWrite, isZeroClear, hk']

private lemma clear_count (env : Env) (s : Sys) (cl : Claim)
    (hd : s.n.depositHappened cl.chainId cl.l2TxHash = env.txDataHash cl.triple)
    (c : ChainId) (h : Bytes32) :
    [Event.clear cl s.n.l1AssetRouter].countP (isClear c h) + occupied (afterClaim s cl).n c h =
      [Event.clear cl s.n.l1AssetRouter].countP (isNzWrite c h) +
        [Event.clear cl s.n.l1AssetRouter].countP (isZeroClear env c h) + occupied s.n c h := by
  by_cases hk : cl.chainId = c ∧ cl.l2TxHash = h
  · obtain ⟨rfl, rfl⟩ := hk
    by_cases hz : env.txDataHash cl.triple = 0 <;>
      simp [afterClaim, occupied, isClear, isNzWrite, isZeroClear, hd, hz]
  · have hk' : ¬ (cl.chainId = c ∧ cl.l2TxHash = h ∧ env.txDataHash cl.triple = 0) :=
      fun ⟨a, b, _⟩ => hk ⟨a, b⟩
    simp only [afterClaim, occupied, setSlot_other _ _ hk]
    simp [isClear, isNzWrite, isZeroClear, hk, hk']

private lemma step_count {env : Env} {cfg : Cfg} {s s' : Sys} {l : Label}
    (hs : Step Checks.source env cfg s l s') (c : ChainId) (h : Bytes32) :
    ∃ Δ : List Event, s'.log = s.log ++ Δ ∧
      Δ.countP (isClear c h) + occupied s'.n c h =
        Δ.countP (isNzWrite c h) + Δ.countP (isZeroClear env c h) + occupied s.n c h := by
  cases hs with
  | forwarded _ _ _ hex => exact ⟨_, rfl, write_count env s _ _ _ _ (hex rfl) c h⟩
  | twoBridges _ _ _ hex => exact ⟨_, rfl, write_count env s _ _ _ _ (hex rfl) c h⟩
  | confirm _ hok => exact ⟨_, rfl, clear_count env s _ (hok.dataHash rfl) c h⟩
  | recover _ hok => exact ⟨_, rfl, clear_count env s _ (hok.dataHash rfl) c h⟩
  | routerConfirm =>
    exact ⟨[.handler _ _ _], rfl, by simp [occupied, isClear, isNzWrite, isZeroClear]⟩
  | _ => exact ⟨[], by simp, by simp [occupied]⟩

theorem ClearCountIdentity : Properties.ClearCountIdentity := by
  intro env cfg s0 s h0 hr c h
  induction hr with
  | refl => simp [h0]
  | step _ hs ih =>
    obtain ⟨Δ, hl, hΔ⟩ := step_count hs c h
    rw [hl, List.countP_append, List.countP_append, List.countP_append]
    omega

theorem AtMostOneClearPerDeposit : Properties.AtMostOneClearPerDeposit := by
  intro env cfg s0 s c h h0 hr hw hz
  have := ClearCountIdentity env cfg s0 s h0 hr c h
  omega

/-! ## Backing -/

/-- Every slot is empty, holds its start value, or holds a value some logged write put there. -/
private def Prov (n0 : Nullifier) (s : Sys) : Prop :=
  ∀ c h, s.n.depositHappened c h = 0 ∨ s.n.depositHappened c h = n0.depositHappened c h ∨
    ∃ o, Event.write o c h (s.n.depositHappened c h) ∈ s.log

/-- Every clear in the log `L` is backed by its prefix. -/
private def BackedL (env : Env) (n0 : Nullifier) (L : List Event) : Prop :=
  ∀ (pre post : List Event) (cl : Claim) (tgt : Address),
    L = pre ++ Event.clear cl tgt :: post → Backed env n0 pre cl

private lemma split_last {pre post L : List Event} {e x : Event}
    (h : pre ++ e :: post = L ++ [x]) :
    (pre = L ∧ e = x) ∨ ∃ post', L = pre ++ e :: post' := by
  rcases List.eq_nil_or_concat' post with hp | ⟨post', y, hp⟩
  · subst hp
    have := List.append_inj' h rfl
    exact Or.inl ⟨this.1, by simpa using this.2⟩
  · subst hp
    have h' : (pre ++ e :: post') ++ [y] = L ++ [x] := by
      rw [List.append_assoc, List.cons_append]; exact h
    exact Or.inr ⟨post', (List.append_inj' h' rfl).1.symm⟩

private lemma backedL_nonclear {env : Env} {n0 : Nullifier} {L : List Event} {x : Event}
    (hb : BackedL env n0 L) (hx : ∀ cl tgt, x ≠ .clear cl tgt) : BackedL env n0 (L ++ [x]) := by
  intro pre post cl tgt hL
  rcases split_last hL.symm with ⟨_, he⟩ | ⟨post', hL'⟩
  · exact absurd he.symm (hx cl tgt)
  · exact hb pre post' cl tgt hL'

private lemma backedL_clear {env : Env} {n0 : Nullifier} {L : List Event} {cl : Claim}
    {tgt : Address} (hb : BackedL env n0 L) (hcl : Backed env n0 L cl) :
    BackedL env n0 (L ++ [.clear cl tgt]) := by
  intro pre post cl' tgt' hL
  rcases split_last hL.symm with ⟨hp, he⟩ | ⟨post', hL'⟩
  · cases he; subst hp; exact hcl
  · exact hb pre post' cl' tgt' hL'

private lemma prov_write {n0 : Nullifier} {s : Sys} (hp : Prov n0 s) (o : Origin) (c' : ChainId)
    (h' v : Bytes32) : Prov n0 (afterWrite s o c' h' v) := by
  intro c h
  by_cases hk : c' = c ∧ h' = h
  · obtain ⟨rfl, rfl⟩ := hk
    exact Or.inr (Or.inr ⟨o, by simp [afterWrite]⟩)
  · have hs : (afterWrite s o c' h' v).n.depositHappened c h = s.n.depositHappened c h :=
      setSlot_other _ _ hk
    rw [hs]
    rcases hp c h with h1 | h1 | ⟨o', h1⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨o', List.mem_append_left _ h1⟩)

private lemma prov_clear {n0 : Nullifier} {s : Sys} (hp : Prov n0 s) (cl : Claim) :
    Prov n0 (afterClaim s cl) := by
  intro c h
  by_cases hk : cl.chainId = c ∧ cl.l2TxHash = h
  · obtain ⟨rfl, rfl⟩ := hk
    exact Or.inl (by simp [afterClaim])
  · have hs : (afterClaim s cl).n.depositHappened c h = s.n.depositHappened c h :=
      setSlot_other _ _ hk
    rw [hs]
    rcases hp c h with h1 | h1 | ⟨o', h1⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨o', List.mem_append_left _ h1⟩)

private lemma claim_backed {env : Env} {n0 : Nullifier} {s : Sys} {cl : Claim} (hp : Prov n0 s)
    (hd : s.n.depositHappened cl.chainId cl.l2TxHash = env.txDataHash cl.triple) :
    Backed env n0 s.log cl := by
  rcases hp cl.chainId cl.l2TxHash with h1 | h1 | ⟨o, h1⟩
  · exact Or.inl (hd.symm.trans h1)
  · exact Or.inr (Or.inl (h1.symm.trans hd))
  · exact Or.inr (Or.inr ⟨o, hd ▸ h1⟩)

private lemma step_backed {env : Env} {cfg : Cfg} {n0 : Nullifier} {s s' : Sys} {l : Label}
    (hs : Step Checks.source env cfg s l s') (hp : Prov n0 s) (hb : BackedL env n0 s.log) :
    Prov n0 s' ∧ BackedL env n0 s'.log := by
  cases hs with
  | forwarded =>
    exact ⟨prov_write hp _ _ _ _, backedL_nonclear hb (fun _ _ => Event.noConfusion)⟩
  | twoBridges =>
    exact ⟨prov_write hp _ _ _ _, backedL_nonclear hb (fun _ _ => Event.noConfusion)⟩
  | confirm _ hok =>
    exact ⟨prov_clear hp _, backedL_clear hb (claim_backed hp (hok.dataHash rfl))⟩
  | recover _ hok =>
    exact ⟨prov_clear hp _, backedL_clear hb (claim_backed hp (hok.dataHash rfl))⟩
  | routerConfirm =>
    refine ⟨fun c h => ?_, backedL_nonclear hb (fun _ _ => Event.noConfusion)⟩
    rcases hp c h with h1 | h1 | ⟨o', h1⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨o', List.mem_append_left _ h1⟩)
  | _ => exact ⟨hp, hb⟩

private lemma reach_backed {env : Env} {cfg : Cfg} {s0 s : Sys} (h0 : s0.log = [])
    (hr : Reach Checks.source env cfg s0 s) : Prov s0.n s ∧ BackedL env s0.n s.log := by
  induction hr with
  | refl =>
    refine ⟨fun c h => Or.inr (Or.inl rfl), ?_⟩
    intro pre post cl tgt hL
    rw [h0] at hL
    simp at hL
  | step _ hs ih => exact step_backed hs ih.1 ih.2

theorem ClearsAreBacked : Properties.ClearsAreBacked := by
  intro env cfg s0 s h0 hr pre post cl tgt hL
  exact (reach_backed h0 hr).2 pre post cl tgt hL

/-! ## Origins of writes -/

/-- Every logged write is a direct write by the current, non-router, nonzero `l1AssetRouter`, or a
bridgehub deposit of its triple's hash, or a zero counterpart record. -/
private def Orig (env : Env) (cfg : Cfg) (s : Sys) : Prop :=
  ∀ (o : Origin) (c : ChainId) (h v : Bytes32), Event.write o c h v ∈ s.log →
    (∃ a, o = .direct a ∧ a = s.n.l1AssetRouter ∧ a ≠ cfg.router ∧ a ≠ 0) ∨
      (∃ t, o = .deposit t ∧ v = env.txDataHash t) ∨ (o = .counterpart ∧ v = 0)

private lemma orig_mono {env : Env} {cfg : Cfg} {s s' : Sys} (ho : Orig env cfg s)
    (hrt : s'.n.l1AssetRouter = s.n.l1AssetRouter)
    (hnew : ∀ o c h v, Event.write o c h v ∈ s'.log → Event.write o c h v ∈ s.log ∨
      ((∃ a, o = .direct a ∧ a = s.n.l1AssetRouter ∧ a ≠ cfg.router ∧ a ≠ 0) ∨
        (∃ t, o = .deposit t ∧ v = env.txDataHash t) ∨ (o = .counterpart ∧ v = 0))) :
    Orig env cfg s' := by
  intro o c h v hm
  rw [hrt]
  rcases hnew o c h v hm with hm | hm
  · exact ho o c h v hm
  · exact hm

private lemma step_orig {env : Env} {cfg : Cfg} {s s' : Sys} {l : Label}
    (hs : Step Checks.source env cfg s l s') (ho : Orig env cfg s) : Orig env cfg s' := by
  cases hs with
  | setL1AssetRouter _ _ h0 _ =>
    intro o c h v hm
    rcases ho o c h v hm with ⟨a, _, ha, _, hne⟩ | hm' | hm'
    · exact absurd (ha.trans h0) hne
    · exact Or.inr (Or.inl hm')
    · exact Or.inr (Or.inr hm')
  | forwarded hsnd ha _ _ =>
    refine orig_mono ho rfl (fun o c h v hm => ?_)
    simp only [afterWrite, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | hm
    · exact Or.inl hm
    · cases hm
      exact Or.inr (Or.inl ⟨_, rfl, ha, hsnd.2.2.1, hsnd.1⟩)
  | @twoBridges caller _ req _ _ _ _ _ =>
    refine orig_mono ho rfl (fun o c h v hm => ?_)
    simp only [afterWrite, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | hm
    · exact Or.inl hm
    · cases hm
      cases req with
      | deposit a d => exact Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩))
      | counterpart => exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  | confirm =>
    refine orig_mono ho rfl (fun o c h v hm => ?_)
    simp only [afterClaim, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hm
    exact Or.inl hm
  | recover =>
    refine orig_mono ho rfl (fun o c h v hm => ?_)
    simp only [afterClaim, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hm
    exact Or.inl hm
  | routerConfirm =>
    refine orig_mono ho rfl (fun o c h v hm => ?_)
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hm
    exact Or.inl hm
  | _ => exact ho

private lemma reach_orig {env : Env} {cfg : Cfg} {s0 s : Sys} (h0 : s0.log = [])
    (hr : Reach Checks.source env cfg s0 s) : Orig env cfg s := by
  induction hr with
  | refl => intro o c h v hm; rw [h0] at hm; simp at hm
  | step _ hs ih => exact step_orig hs ih

theorem RecordsComeFromBridgehub : Properties.RecordsComeFromBridgehub := by
  intro env cfg s0 s h0 hr hcfg o c h v hm
  rcases reach_orig h0 hr o c h v hm with ⟨a, _, ha, hr', hz⟩ | hm' | hm'
  · rcases hcfg with h1 | h1
    · exact absurd (ha.trans h1) hz
    · exact absurd (ha.trans h1) hr'
  · exact Or.inl hm'
  · exact Or.inr hm'

theorem ClearCarriesDepositTriple : Properties.ClearCarriesDepositTriple := by
  intro env cfg s0 s h0 hr hcfg pre post cl tgt hL hfresh hnz
  have hdep : ∃ t, Event.write (.deposit t) cl.chainId cl.l2TxHash (env.txDataHash t) ∈ pre ∧
      env.txDataHash t = env.txDataHash cl.triple := by
    rcases ClearsAreBacked env cfg s0 s h0 hr pre post cl tgt hL with hb | hb | ⟨o, hb⟩
    · exact absurd hb hnz
    · exact absurd (hfresh.symm.trans hb).symm hnz
    · have hm : Event.write o cl.chainId cl.l2TxHash (env.txDataHash cl.triple) ∈ s.log := by
        rw [hL]; exact List.mem_append_left _ hb
      rcases RecordsComeFromBridgehub env cfg s0 s h0 hr hcfg _ _ _ _ hm with
        ⟨t, rfl, ht⟩ | ⟨_, hz⟩
      · exact ⟨t, ht ▸ hb, ht.symm⟩
      · exact absurd hz hnz
  refine ⟨hdep, fun hinj => ?_⟩
  obtain ⟨t, ht, heq⟩ := hdep
  have hm : Event.write (.deposit t) cl.chainId cl.l2TxHash (env.txDataHash t) ∈ s.log := by
    rw [hL]; exact List.mem_append_left _ ht
  have := hinj t hm heq
  subst this
  exact ht

/-! ## Status -/

private def Accepted (env : Env) (s : Sys) : Prop :=
  ∀ (cl : Claim) (tgt : Address), Event.clear cl tgt ∈ s.log → env.accepts cl.query

private lemma step_accepted {env : Env} {cfg : Cfg} {s s' : Sys} {l : Label}
    (hs : Step Checks.source env cfg s l s') (ha : Accepted env s) : Accepted env s' := by
  cases hs with
  | forwarded =>
    intro cl tgt hm
    simp only [afterWrite, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hm
    exact ha cl tgt hm
  | twoBridges =>
    intro cl tgt hm
    simp only [afterWrite, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hm
    exact ha cl tgt hm
  | confirm _ hok =>
    intro cl tgt hm
    simp only [afterClaim, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | hm
    · exact ha cl tgt hm
    · cases hm; exact hok.proof rfl
  | recover _ hok =>
    intro cl tgt hm
    simp only [afterClaim, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | hm
    · exact ha cl tgt hm
    · cases hm; exact hok.proof rfl
  | routerConfirm =>
    intro cl tgt hm
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hm
    exact ha cl tgt hm
  | _ => exact ha

private lemma reach_accepted {env : Env} {cfg : Cfg} {s0 s : Sys} (h0 : s0.log = [])
    (hr : Reach Checks.source env cfg s0 s) : Accepted env s := by
  induction hr with
  | refl => intro cl tgt hm; rw [h0] at hm; simp at hm
  | step _ hs ih => exact step_accepted hs ih

theorem ClearStatusIsTrue : Properties.ClearStatusIsTrue := by
  intro env cfg s0 s truth hsound h0 hr cl tgt hm
  exact hsound _ (reach_accepted h0 hr cl tgt hm)

theorem NoFailureClearOfSucceededDeposit : Properties.NoFailureClearOfSucceededDeposit := by
  intro env cfg s0 s truth hsound h0 hr
  have hst := ClearStatusIsTrue env cfg s0 s truth hsound h0 hr
  refine ⟨fun cl tgt hm hsucc => ?_, fun cl cl' tgt tgt' hm hm' hc hh => ?_⟩
  · have := hst cl tgt hm
    rw [hsucc] at this
    exact (Option.some.inj this).symm
  · have h1 := hst cl tgt hm
    have h2 := hst cl' tgt' hm'
    rw [hc, hh, h2] at h1
    exact (Option.some.inj h1).symm

/-! ## Record and clear -/

theorem DepositRecordsClaimClears : Properties.DepositRecordsClaimClears := by
  intro env cfg s s' l hs
  constructor
  · intro caller c a d h hl
    subst hl
    cases hs with
    | twoBridges => simp [afterWrite, SecondBridge.hash]
  · intro a cl hl
    rcases hl with rfl | rfl
    · cases hs with
      | confirm => simp [afterClaim]
    · cases hs with
      | recover => simp [afterClaim, Claim.asFailure]

/-! ## The router's handler call -/

theorem NoHandlerCallWithoutClear : Properties.NoHandlerCallWithoutClear := by
  intro env cfg s0 s h0 hr
  induction hr with
  | refl => simp [h0]
  | step _ hs ih =>
    cases hs with
    | routerConfirm hsnd honly _ => exact absurd (honly rfl) hsnd.2.1
    | forwarded => simp [afterWrite, List.countP_append, ih, isHandler]
    | twoBridges => simp [afterWrite, List.countP_append, ih, isHandler]
    | confirm => simp [afterClaim, List.countP_append, ih, isHandler]
    | recover => simp [afterClaim, List.countP_append, ih, isHandler]
    | _ => exact ih

/-! ## Records leave only by a preimage -/

theorem RecordLeavesOnlyByPreimage : Properties.RecordLeavesOnlyByPreimage := by
  intro env cfg s s' c h hr hnz hch
  suffices H : ∃ Δ, s'.log = s.log ++ Δ ∧
      (s'.n.depositHappened c h = s.n.depositHappened c h ∨
        ∃ (cl : Claim) (tgt : Address), Event.clear cl tgt ∈ Δ ∧ cl.chainId = c ∧
          cl.l2TxHash = h ∧ env.txDataHash cl.triple = s.n.depositHappened c h) by
    obtain ⟨Δ, hl, h1 | h1⟩ := H
    · exact absurd h1 hch
    · exact ⟨Δ, hl, h1⟩
  clear hch
  induction hr with
  | refl => exact ⟨[], by simp, Or.inl rfl⟩
  | @step t u l _ hs ih =>
    obtain ⟨Δ, hl, ih⟩ := ih
    obtain ⟨Δ', hl', -⟩ := step_count hs c h
    refine ⟨Δ ++ Δ', by rw [hl', hl, List.append_assoc], ?_⟩
    rcases ih with ih | ⟨cl, tgt, hm, h1, h2, h3⟩
    · rcases step_slot hs c h with h4 | h4 | ⟨cl, hlog, h1, h2, h3⟩
      · exact Or.inl (h4.trans ih)
      · exact absurd (ih.symm.trans h4) hnz
      · refine Or.inr ⟨cl, t.n.l1AssetRouter, ?_, h1, h2, h3.trans ih⟩
        have : Δ' = [.clear cl t.n.l1AssetRouter] := by
          rw [hl'] at hlog; exact List.append_cancel_left hlog
        rw [this]; exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact Or.inr ⟨cl, tgt, List.mem_append_left _ hm, h1, h2, h3⟩

/-! ## Configuration and pause -/

theorem DeprecatedSlotsFrozen : Properties.DeprecatedSlotsFrozen := by
  intro chk env cfg s s' hr
  induction hr with
  | refl => rfl
  | step _ hs ih => rw [← ih]; cases hs <;> rfl

private lemma step_config {chk : Checks} {env : Env} {cfg : Cfg} {s s' : Sys} {l : Label}
    (hs : Step chk env cfg s l s') :
    (s'.n.l1AssetRouter = s.n.l1AssetRouter ∨ s.n.l1AssetRouter = 0) ∧
    (s'.n.l1NativeTokenVault = s.n.l1NativeTokenVault ∨ s.n.l1NativeTokenVault = 0) ∧
    (s'.n.l1InteropHandler = s.n.l1InteropHandler ∨ s.n.l1InteropHandler = 0) := by
  cases hs with
  | setL1AssetRouter _ _ h0 _ => exact ⟨Or.inr h0, Or.inl rfl, Or.inl rfl⟩
  | setL1NativeTokenVault _ _ h0 _ => exact ⟨Or.inl rfl, Or.inr h0, Or.inl rfl⟩
  | setL1InteropHandler _ _ h0 _ => exact ⟨Or.inl rfl, Or.inl rfl, Or.inr h0⟩
  | _ => exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

theorem ConfigSetOnce : Properties.ConfigSetOnce := by
  intro chk env cfg s s' hr
  induction hr with
  | refl => exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  | step _ hs ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    obtain ⟨k1, k2, k3⟩ := step_config hs
    refine ⟨fun hne => ?_, fun hne => ?_, fun hne => ?_⟩
    · rcases k1 with k | k
      · exact k.trans (h1 hne)
      · exact absurd ((h1 hne).symm.trans k) hne
    · rcases k2 with k | k
      · exact k.trans (h2 hne)
      · exact absurd ((h2 hne).symm.trans k) hne
    · rcases k3 with k | k
      · exact k.trans (h3 hne)
      · exact absurd ((h3 hne).symm.trans k) hne

private lemma step_initialized {chk : Checks} {env : Env} {cfg : Cfg} {s s' : Sys} {l : Label}
    (hs : Step chk env cfg s l s') (h : s.n.initialized = true) : s'.n.initialized = true := by
  cases hs with
  | «initialize» => rfl
  | forwarded => exact h
  | twoBridges => exact h
  | confirm => exact h
  | recover => exact h
  | _ => exact h

private lemma reach_initialized {chk : Checks} {env : Env} {cfg : Cfg} {s s' : Sys}
    (hr : Reach chk env cfg s s') (h : s.n.initialized = true) : s'.n.initialized = true := by
  induction hr with
  | refl => exact h
  | step _ hs ih => exact step_initialized hs ih

theorem InitializeOnlyOnce : Properties.InitializeOnlyOnce := by
  intro chk env cfg s s' s'' t a o a' o' h1 hr h2
  have hi : s'.n.initialized = true := by cases h1; rfl
  have hi'' : s''.n.initialized = true := reach_initialized hr hi
  cases h2 with
  | «initialize» _ hni _ => exact absurd (hi''.symm.trans hni) Bool.noConfusion

theorem RouterPausedStepKeepsRecords : Properties.RouterPausedStepKeepsRecords := by
  intro env cfg s s' l hs hrp hrt
  cases hs with
  | forwarded hsnd ha => exact absurd (ha.trans hrt) hsnd.2.2.1
  | twoBridges hr => exact absurd (hrp.symm.trans hr) Bool.noConfusion
  | confirm _ hok => exact absurd (hrp.symm.trans (hok.routerLive hrt)) Bool.noConfusion
  | recover _ hok => exact absurd (hrp.symm.trans (hok.routerLive hrt)) Bool.noConfusion
  | _ => rfl

theorem PausedStepKeepsRecords : Properties.PausedStepKeepsRecords := by
  intro env cfg s s' l hs hp
  cases hs with
  | forwarded _ _ hnp _ => exact absurd (hp.symm.trans hnp) Bool.noConfusion
  | twoBridges _ _ hnp _ => exact absurd (hp.symm.trans hnp) Bool.noConfusion
  | confirm _ hok => exact absurd (hp.symm.trans hok.notPaused) Bool.noConfusion
  | recover _ hok => exact absurd (hp.symm.trans hok.notPaused) Bool.noConfusion
  | pause _ _ hnp => exact absurd (hp.symm.trans hnp) Bool.noConfusion
  | unpause _ ha _ => exact ⟨rfl, fun _ => by rw [ha]⟩
  | _ => exact ⟨rfl, fun h => absurd (hp.symm.trans h) Bool.noConfusion⟩

theorem PausedOwnerlessFreezesForever : Properties.PausedOwnerlessFreezesForever := by
  intro env cfg s s' hr hi hp ho hpo
  suffices H : s'.n.initialized = true ∧ s'.n.paused = true ∧ s'.n.owner = 0 ∧
      s'.n.pendingOwner = 0 ∧ s'.n.depositHappened = s.n.depositHappened from ⟨H.2.1, H.2.2.2.2⟩
  induction hr with
  | refl => exact ⟨hi, hp, ho, hpo, rfl⟩
  | step _ hs ih =>
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih
    cases hs with
    | «initialize» _ hni _ => exact absurd (i1.symm.trans hni) Bool.noConfusion
    | transferOwnership hsnd ha => exact absurd (ha.trans i3) hsnd.1
    | acceptOwnership hsnd ha => exact absurd (ha.trans i4) hsnd.1
    | renounceOwnership hsnd ha => exact absurd (ha.trans i3) hsnd.1
    | setL1NativeTokenVault hsnd ha => exact absurd (ha.trans i3) hsnd.1
    | setL1AssetRouter hsnd ha => exact absurd (ha.trans i3) hsnd.1
    | setL1InteropHandler hsnd ha => exact absurd (ha.trans i3) hsnd.1
    | pause hsnd ha => exact absurd (ha.trans i3) hsnd.1
    | unpause hsnd ha => exact absurd (ha.trans i3) hsnd.1
    | forwarded _ _ hnp _ => exact absurd (i2.symm.trans hnp) Bool.noConfusion
    | twoBridges _ _ hnp _ => exact absurd (i2.symm.trans hnp) Bool.noConfusion
    | confirm _ hok => exact absurd (i2.symm.trans hok.notPaused) Bool.noConfusion
    | recover _ hok => exact absurd (i2.symm.trans hok.notPaused) Bool.noConfusion
    | routerConfirm => exact ⟨i1, i2, i3, i4, i5⟩
    | routerSetPaused => exact ⟨i1, i2, i3, i4, i5⟩

/-! ## Records stay until cleared -/

/-- Each step appends at most one event to the log. -/
private lemma step_log {chk : Checks} {env : Env} {cfg : Cfg} {s s' : Sys} {l : Label}
    (hs : Step chk env cfg s l s') : s'.log = s.log ∨ ∃ e, s'.log = s.log ++ [e] := by
  cases hs with
  | forwarded => exact Or.inr ⟨_, rfl⟩
  | twoBridges => exact Or.inr ⟨_, rfl⟩
  | confirm => exact Or.inr ⟨_, rfl⟩
  | recover => exact Or.inr ⟨_, rfl⟩
  | routerConfirm => exact Or.inr ⟨_, rfl⟩
  | _ => exact Or.inl rfl

/-- A run from an empty log passes through the step that appended any one of its events. -/
private lemma reach_split {chk : Checks} {env : Env} {cfg : Cfg} {s0 s : Sys} (h0 : s0.log = [])
    (hr : Reach chk env cfg s0 s) :
    ∀ (pre post : List Event) (e : Event), s.log = pre ++ e :: post →
      ∃ (t t' : Sys) (l : Label), Reach chk env cfg s0 t ∧ Step chk env cfg t l t' ∧
        t.log = pre ∧ t'.log = pre ++ [e] ∧ Reach chk env cfg t' s := by
  induction hr with
  | refl =>
    intro pre post e hl
    rw [h0] at hl
    exact absurd hl.symm (by simp)
  | @step t u l hr' hs ih =>
    intro pre post e hl
    rcases step_log hs with hu | ⟨x, hu⟩
    · obtain ⟨a, a', l', r1, st, la, la', r2⟩ := ih pre post e (hu ▸ hl)
      exact ⟨a, a', l', r1, st, la, la', .step r2 hs⟩
    · rw [hu] at hl
      rcases split_last hl.symm with ⟨hp, he⟩ | ⟨post', hL⟩
      · subst he
        exact ⟨t, u, l, hr', hs, hp.symm, by rw [hu, hp], .refl _⟩
      · obtain ⟨a, a', l', r1, st, la, la', r2⟩ := ih pre post' e hL
        exact ⟨a, a', l', r1, st, la, la', .step r2 hs⟩

/-- A step that appends a write of `v` at `(c, h)` leaves `v` there. -/
private lemma step_write_slot {chk : Checks} {env : Env} {cfg : Cfg} {s s' : Sys} {l : Label}
    {o : Origin} {c : ChainId} {h v : Bytes32} (hs : Step chk env cfg s l s')
    (hl : s'.log = s.log ++ [.write o c h v]) : s'.n.depositHappened c h = v := by
  cases hs with
  | forwarded =>
    simp only [afterWrite, List.append_cancel_left_eq, List.cons.injEq, Event.write.injEq,
      and_true] at hl
    obtain ⟨-, rfl, rfl, rfl⟩ := hl
    simp [afterWrite]
  | twoBridges =>
    simp only [afterWrite, List.append_cancel_left_eq, List.cons.injEq, Event.write.injEq,
      and_true] at hl
    obtain ⟨-, rfl, rfl, rfl⟩ := hl
    simp [afterWrite]
  | confirm => simp [afterClaim] at hl
  | recover => simp [afterClaim] at hl
  | routerConfirm => simp at hl
  | _ => exact absurd hl (by simp)

theorem RecordStaysUntilCleared : Properties.RecordStaysUntilCleared := by
  intro env cfg s0 s h0 hr pre post o c h v hl hv hpost
  obtain ⟨t, t', l, -, st, htl, ht', r2⟩ := reach_split h0 hr pre post _ hl
  have hslot : t'.n.depositHappened c h = v := step_write_slot st (by rw [ht', htl])
  by_contra hne
  obtain ⟨Δ, hΔ, cl, tgt, hm, h1, h2, -⟩ :=
    RecordLeavesOnlyByPreimage env cfg t' s c h r2 (hslot ▸ hv) (hslot ▸ hne)
  have hΔ' : Δ = post := by
    rw [hl, ht', List.append_assoc, List.singleton_append] at hΔ
    simpa using (List.append_cancel_left hΔ).symm
  subst hΔ'
  exact (List.countP_eq_zero.mp hpost) _ hm (by simp [isClear, h1, h2])

theorem UnclaimedDepositRecoverable : Properties.UnclaimedDepositRecoverable := by
  intro env cfg s0 s h0 hr pre post t c h hl hnz hpost hp hrt hrp a cl ha hc hh ht hacc
  have hslot : s.n.depositHappened c h = env.txDataHash t :=
    RecordStaysUntilCleared env cfg s0 s h0 hr pre post _ c h _ hl hnz hpost
  subst hc hh ht
  refine ⟨Step.recover ha ⟨hp, fun _ => hacc, fun _ => hslot, fun _ => hrp⟩, ?_, ?_⟩
  · simp [afterClaim, Claim.asFailure]
  · simp [afterClaim, hrt]

/-! ## Who configures -/

theorem OnlyOwnerPausesOrConfigures : Properties.OnlyOwnerPausesOrConfigures := by
  intro chk env cfg s s' l hs
  cases hs with
  | «initialize» _ hni _ => exact ⟨fun h => by simp at h, fun _ => Or.inl ⟨_, _, rfl, hni⟩⟩
  | transferOwnership => exact ⟨fun h => by simp at h, fun h => by simp at h⟩
  | acceptOwnership _ ha => exact ⟨fun h => by simp at h, fun _ => Or.inr (Or.inl (by rw [ha]))⟩
  | renounceOwnership _ ha => exact ⟨fun h => by simp at h, fun _ => Or.inr (Or.inr (by rw [ha]))⟩
  | setL1NativeTokenVault hsnd ha =>
    exact ⟨fun _ => ⟨by simp [Label.ownerCaller, ha], ha ▸ hsnd.1⟩, fun h => by simp at h⟩
  | setL1AssetRouter hsnd ha =>
    exact ⟨fun _ => ⟨by simp [Label.ownerCaller, ha], ha ▸ hsnd.1⟩, fun h => by simp at h⟩
  | setL1InteropHandler hsnd ha =>
    exact ⟨fun _ => ⟨by simp [Label.ownerCaller, ha], ha ▸ hsnd.1⟩, fun h => by simp at h⟩
  | pause hsnd ha => exact ⟨fun _ => ⟨by simp [Label.ownerCaller, ha], ha ▸ hsnd.1⟩, fun h => by simp at h⟩
  | unpause hsnd ha => exact ⟨fun _ => ⟨by simp [Label.ownerCaller, ha], ha ▸ hsnd.1⟩, fun h => by simp at h⟩
  | forwarded => exact ⟨fun h => by simp [afterWrite] at h, fun h => by simp [afterWrite] at h⟩
  | twoBridges => exact ⟨fun h => by simp [afterWrite] at h, fun h => by simp [afterWrite] at h⟩
  | confirm => exact ⟨fun h => by simp [afterClaim] at h, fun h => by simp [afterClaim] at h⟩
  | recover => exact ⟨fun h => by simp [afterClaim] at h, fun h => by simp [afterClaim] at h⟩
  | routerConfirm => exact ⟨fun h => by simp at h, fun h => by simp at h⟩
  | routerSetPaused => exact ⟨fun h => by simp at h, fun h => by simp at h⟩

/-! ## Concrete worlds -/

private def ledgerZeroDeprecated : Deprecated :=
  ⟨0, 0, 0, 0, 0, fun _ => 0, fun _ _ _ => false, fun _ => false, fun _ _ => 0, 0, 0⟩

/-- Fresh proxy storage: everything zero, not initialized. -/
private def ledgerFresh : Sys :=
  ⟨⟨false, 0, 0, false, fun _ _ => 0, 0, 0, 0, ledgerZeroDeprecated⟩, false, []⟩

/-- Nullifier `1`, router `2`, bridgehub `3`. -/
private def ledgerCfg : Cfg := ⟨1, 2, 3⟩

/-- Deposit A: sender `10`, asset `11`, data `[1]`. Deposit B: sender `12`, asset `11`, data `[2]`. -/
private def ledgerTripleA : Triple := ⟨10, 11, [1]⟩
private def ledgerTripleB : Triple := ⟨12, 11, [2]⟩

/-- A hash that is never zero and separates A and B. -/
private def ledgerHash (t : Triple) : Bytes32 :=
  if t = ledgerTripleA then 7 else if t = ledgerTripleB then 8 else 9

/-- The real statuses: transaction `9` on chain `5` failed, transaction `13` on chain `5`
succeeded. -/
private def ledgerTruth (c : ChainId) (h : Bytes32) : Option TxStatus :=
  if c = 5 ∧ h = 9 then some .failure else if c = 5 ∧ h = 13 then some .success else none

/-- The prover accepts exactly the queries naming the real status. -/
private def ledgerEnv : Env := ⟨ledgerHash, fun q => ledgerTruth q.chainId q.l2TxHash = some q.status⟩

private lemma ledgerEnv_sound : ∀ q, ledgerEnv.accepts q → ledgerTruth q.chainId q.l2TxHash = some q.status :=
  fun _ h => h

/-- A's recovery (transaction `9`, failed) and B's confirmation (transaction `13`, succeeded). -/
private def ledgerClaimA : Claim := ⟨5, 10, 3, .failure, 11, [1], 9, 1, 4, [6]⟩
private def ledgerClaimB : Claim := ⟨5, 12, 5, .success, 11, [2], 13, 1, 8, [6]⟩
/-- A second, different claim of A's key and triple (another batch number). -/
private def ledgerClaimA' : Claim := ⟨5, 10, 3, .failure, 11, [1], 9, 2, 4, [6]⟩

private lemma ledger_ext10 : ExternalSender ledgerCfg 10 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide
private lemma ledger_ext12 : ExternalSender ledgerCfg 12 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide
private lemma ledger_ext20 : ExternalSender ledgerCfg 20 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- After `initialize(10)` by `10` and `setL1AssetRouter(2)` by `10`. -/
private def ledgerConfigured : Sys :=
  ⟨⟨true, 10, 0, false, fun _ _ => 0, 2, 0, 0, ledgerZeroDeprecated⟩, false, []⟩

private lemma ledger_reach_configured (chk : Checks) (env : Env) :
    Reach chk env ledgerCfg ledgerFresh ledgerConfigured :=
  .step (.step (.refl _) (Step.initialize ledger_ext10 rfl (by decide)))
    (Step.setL1AssetRouter ledger_ext10 rfl rfl (by decide))

/-- The bridgehub deposit of `t`'s asset and data by `t`'s sender at `(5, h)`. -/
private def ledgerDeposit (env : Env) (s : Sys) (t : Triple) (h : Bytes32) : Sys :=
  afterWrite s (.deposit t) 5 h (env.txDataHash t)

private lemma ledger_step_deposit (chk : Checks) (env : Env) (s : Sys) (t : Triple) (h : Bytes32)
    (hr : s.routerPaused = false) (hrt : s.n.l1AssetRouter = 2) (hp : s.n.paused = false)
    (hx : chk.depositExists = true → s.n.depositHappened 5 h = 0) :
    Step chk env ledgerCfg s (.twoBridges t.sender 5 (.deposit t.assetId t.data) h)
      (ledgerDeposit env s t h) :=
  Step.twoBridges hr hrt.symm hp hx

private lemma ledgerHash_A : ledgerHash ledgerTripleA = 7 := by simp [ledgerHash]
private lemma ledgerHash_B : ledgerHash ledgerTripleB = 8 := by
  simp [ledgerHash, ledgerTripleA, ledgerTripleB]

/-- The run of `LedgerRunWitness`, up to the two deposits. -/
private def ledgerTwoDeposits : Sys :=
  ledgerDeposit ledgerEnv (ledgerDeposit ledgerEnv ledgerConfigured ledgerTripleA 9) ledgerTripleB 13

private lemma ledger_reach_two_deposits :
    Reach Checks.source ledgerEnv ledgerCfg ledgerFresh ledgerTwoDeposits :=
  .step (.step (ledger_reach_configured _ _)
    (ledger_step_deposit _ _ _ ledgerTripleA 9 rfl rfl rfl (fun _ => rfl)))
    (ledger_step_deposit _ _ _ ledgerTripleB 13 rfl rfl rfl
      (fun _ => by simp [ledgerDeposit, afterWrite, setSlot, ledgerConfigured]))

private lemma ledger_claimA_ok (s : Sys) (hp : s.n.paused = false) (hr : s.routerPaused = false)
    (hd : s.n.depositHappened 5 9 = 7) :
    ClaimOk Checks.source ledgerEnv ledgerCfg s ledgerClaimA.asFailure :=
  ⟨hp, fun _ => by simp [ledgerEnv, ledgerTruth, ledgerClaimA, Claim.asFailure, Claim.query],
    fun _ => by
      simp only [ledgerClaimA, Claim.asFailure, Claim.triple, ledgerEnv]
      rw [hd]; exact ledgerHash_A.symm,
    fun _ => hr⟩

private lemma ledger_claimB_ok (s : Sys) (hp : s.n.paused = false) (hr : s.routerPaused = false)
    (hd : s.n.depositHappened 5 13 = 8) :
    ClaimOk Checks.source ledgerEnv ledgerCfg s ledgerClaimB :=
  ⟨hp, fun _ => by simp [ledgerEnv, ledgerTruth, ledgerClaimB, Claim.query],
    fun _ => by
      simp only [ledgerClaimB, Claim.triple, ledgerEnv]
      rw [hd]; exact ledgerHash_B.symm,
    fun _ => hr⟩

/-- The full run of `LedgerRunWitness`. -/
private def ledgerRunEnd : Sys :=
  afterClaim (afterClaim ledgerTwoDeposits ledgerClaimA.asFailure) ledgerClaimB

private lemma ledger_reach_run_end :
    Reach Checks.source ledgerEnv ledgerCfg ledgerFresh ledgerRunEnd :=
  .step (.step ledger_reach_two_deposits
    (Step.recover ledger_ext10 (ledger_claimA_ok _ rfl rfl (by
      simp [ledgerTwoDeposits, ledgerDeposit, afterWrite, setSlot, ledgerEnv, ledgerHash_A]))))
    (Step.confirm ledger_ext12 (ledger_claimB_ok _ rfl rfl (by
      simp [ledgerTwoDeposits, ledgerDeposit, afterClaim, afterWrite, setSlot, ledgerEnv,
        ledgerHash_B, ledgerClaimA, Claim.asFailure])))

theorem LedgerRunWitness : Properties.LedgerRunWitness := by
  refine ⟨ledgerEnv, ledgerCfg, ledgerFresh, ledgerRunEnd, ledgerTruth, ledgerClaimA, ledgerClaimB,
    fun _ => Iff.rfl, rfl, rfl, fun _ _ => rfl, ledger_reach_run_end, rfl, ?_, rfl, ?_, rfl, ?_,
    by decide, by decide, ?_, ?_, ?_⟩
  · rfl
  · simp [ledgerTruth, ledgerClaimA]
  · simp [ledgerTruth, ledgerClaimB]
  · simp [ledgerEnv, ledgerClaimA, Claim.triple, ledgerHash, ledgerTripleA]
  · simp [ledgerEnv, ledgerClaimB, Claim.triple, ledgerHash, ledgerTripleA, ledgerTripleB]
  · simp [ledgerEnv, ledgerClaimA, ledgerClaimB, Claim.triple, ledgerHash, ledgerTripleA,
      ledgerTripleB]

/-- After deposit A at `(5, 9)`. -/
private def ledgerOneDeposit (env : Env) : Sys := ledgerDeposit env ledgerConfigured ledgerTripleA 9

private lemma ledger_reach_one_deposit (chk : Checks) (env : Env) :
    Reach chk env ledgerCfg ledgerFresh (ledgerOneDeposit env) :=
  .step (ledger_reach_configured _ _)
    (ledger_step_deposit _ _ _ ledgerTripleA 9 rfl rfl rfl (fun _ => rfl))

theorem PausedOwnerlessReachable : Properties.PausedOwnerlessReachable := by
  have r := Reach.step (Reach.step (ledger_reach_one_deposit Checks.source ledgerEnv)
    (Step.pause ledger_ext10 rfl rfl)) (Step.renounceOwnership ledger_ext10 rfl)
  refine ⟨ledgerEnv, ledgerCfg, ledgerFresh, _, rfl, rfl, fun _ _ => rfl, r, rfl, rfl, rfl, rfl,
    5, 9, ?_⟩
  simp [ledgerOneDeposit, ledgerDeposit, afterWrite, setSlot, ledgerEnv, ledgerHash_A]

theorem HashCheckLoadBearing : Properties.HashCheckLoadBearing := by
  have ok : ∀ s : Sys, s.n.paused = false → s.routerPaused = false →
      ClaimOk { Checks.source with dataHash := false } ledgerEnv ledgerCfg s ledgerClaimA.asFailure :=
    fun s hp hr => ⟨hp, fun _ => by
      simp [ledgerEnv, ledgerTruth, ledgerClaimA, Claim.asFailure, Claim.query],
      fun h => absurd h (by decide), fun _ => hr⟩
  have r := Reach.step (Reach.step (ledger_reach_one_deposit _ ledgerEnv)
    (Step.recover (cl := ledgerClaimA) ledger_ext10 (ok _ rfl rfl)))
    (Step.recover (cl := ledgerClaimA) ledger_ext10 (ok _ rfl rfl))
  refine ⟨ledgerEnv, ledgerCfg, ledgerFresh, _, 5, 9, rfl, r, ?_, ?_, ?_⟩
  · simp [afterClaim, ledgerOneDeposit, ledgerDeposit, afterWrite, isNzWrite, occupied, ledgerFresh,
      ledgerConfigured, ledgerEnv, ledgerHash_A]
  · simp [afterClaim, ledgerOneDeposit, ledgerDeposit, afterWrite, isZeroClear, ledgerConfigured,
      ledgerEnv, ledgerClaimA, Claim.asFailure, Claim.triple, ledgerHash, ledgerTripleA]
  · simp [afterClaim, ledgerOneDeposit, ledgerDeposit, afterWrite, isClear, ledgerConfigured,
      ledgerClaimA, Claim.asFailure]

theorem ProofCheckLoadBearing : Properties.ProofCheckLoadBearing := by
  have r := Reach.step (Reach.step (ledger_reach_configured _ ledgerEnv)
    (ledger_step_deposit { Checks.source with proof := false } ledgerEnv _ ledgerTripleB 13
      rfl rfl rfl (fun _ => rfl)))
    (Step.recover (cl := ledgerClaimB) ledger_ext12
      ⟨rfl, fun h => absurd h (by decide), fun _ => by
        simp [ledgerDeposit, afterWrite, setSlot, ledgerConfigured, ledgerEnv, ledgerClaimB,
          Claim.asFailure, Claim.triple, ledgerTripleB], fun _ => rfl⟩)
  refine ⟨ledgerEnv, ledgerCfg, ledgerFresh, _, ledgerTruth, ledgerEnv_sound, rfl, r,
    ledgerClaimB.asFailure, 2, ?_, ?_, rfl⟩
  · simp [afterClaim, ledgerDeposit, afterWrite, ledgerConfigured]
  · simp [ledgerTruth, ledgerClaimB, Claim.asFailure]

theorem DepositExistsLoadBearing : Properties.DepositExistsLoadBearing := by
  have r := Reach.step (ledger_reach_one_deposit { Checks.source with depositExists := false } ledgerEnv)
    (Step.twoBridges (caller := 12) (c := 5) (h := 9) (req := .deposit 11 [2])
      (chk := { Checks.source with depositExists := false }) rfl rfl rfl
      (fun h => absurd h (by decide)))
  refine ⟨ledgerEnv, ledgerCfg, ledgerFresh, _, 5, 9, rfl, r, ?_⟩
  simp [ledgerOneDeposit, ledgerDeposit, afterWrite, isClear, isNzWrite, isZeroClear, occupied,
    ledgerEnv, SecondBridge.origin, SecondBridge.hash, ledgerFresh, ledgerConfigured, setSlot,
    ledgerHash, ledgerTripleA, ledgerTripleB]

theorem OnlyNullifierLoadBearing : Properties.OnlyNullifierLoadBearing := by
  have r := Reach.step (Reach.refl ledgerFresh)
    (Step.routerConfirm (chk := { Checks.source with onlyNullifier := false }) (env := ledgerEnv)
      (c := 5) (st := .failure) (t := ledgerTripleA) ledger_ext10 (fun h => absurd h (by decide)) rfl)
  refine ⟨ledgerEnv, ledgerCfg, ledgerFresh, _, rfl, r, ?_, fun c h => ?_⟩
  · simp [ledgerFresh, isHandler]
  · simp [ledgerFresh, isClear]

/-- Deposit A, its recovery, deposit A again at the same key, and a recovery with claim `cl'`. -/
private def ledgerRepeated (cl' : Claim) : Sys :=
  afterClaim (ledgerDeposit ledgerEnv (afterClaim (ledgerOneDeposit ledgerEnv) ledgerClaimA.asFailure)
    ledgerTripleA 9) cl'.asFailure

private lemma ledger_reach_repeated (cl' : Claim) (h5 : cl'.chainId = 5) (h9 : cl'.l2TxHash = 9)
    (ht : cl'.triple = ledgerTripleA) :
    Reach Checks.source ledgerEnv ledgerCfg ledgerFresh (ledgerRepeated cl') := by
  have r1 := Reach.step (ledger_reach_one_deposit Checks.source ledgerEnv)
    (Step.recover (cl := ledgerClaimA) ledger_ext10 (ledger_claimA_ok _ rfl rfl (by
      simp [ledgerOneDeposit, ledgerDeposit, afterWrite, setSlot, ledgerEnv, ledgerHash_A])))
  have r2 := Reach.step r1 (ledger_step_deposit _ ledgerEnv _ ledgerTripleA 9 rfl rfl rfl
    (fun _ => by simp [afterClaim, ledgerClaimA, Claim.asFailure]))
  refine Reach.step r2 (Step.recover (cl := cl') ledger_ext10 ⟨rfl, fun _ => ?_, fun _ => ?_, fun _ => rfl⟩)
  · show ledgerTruth cl'.chainId cl'.l2TxHash = some .failure
    rw [h5, h9]; simp [ledgerTruth]
  · show (ledgerDeposit ledgerEnv _ ledgerTripleA 9).n.depositHappened cl'.chainId cl'.l2TxHash =
      ledgerHash cl'.triple
    rw [h5, h9, ht]
    simp [ledgerDeposit, afterWrite, ledgerEnv]

theorem TxHashFreshnessLoadBearing : Properties.TxHashFreshnessLoadBearing := by
  refine ⟨ledgerEnv, ledgerCfg, ledgerFresh, _, ledgerClaimA, rfl, fun _ _ => rfl,
    ledger_reach_repeated ledgerClaimA rfl rfl rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [ledgerEnv, ledgerClaimA, Claim.triple, ledgerHash, ledgerTripleA]
  · simp [ledgerRepeated, afterClaim, ledgerOneDeposit, ledgerDeposit, afterWrite, isNzWrite,
      ledgerConfigured, ledgerEnv, ledgerHash_A, ledgerClaimA]
  · simp [ledgerRepeated, afterClaim, ledgerOneDeposit, ledgerDeposit, afterWrite, isZeroClear,
      ledgerConfigured, ledgerEnv, ledgerClaimA, Claim.asFailure, Claim.triple, ledgerHash,
      ledgerTripleA]
  · simp [ledgerRepeated, afterClaim, ledgerOneDeposit, ledgerDeposit, afterWrite, isClear,
      ledgerConfigured, ledgerClaimA, Claim.asFailure]

theorem SameKeyClearedTwiceWitness : Properties.SameKeyClearedTwiceWitness := by
  refine ⟨ledgerEnv, ledgerCfg, ledgerFresh, _, ledgerTruth, ledgerClaimA, ledgerClaimA',
    fun _ => Iff.rfl, rfl, fun _ _ => rfl, ledger_reach_repeated ledgerClaimA' rfl rfl rfl, ?_,
    by decide, rfl, rfl, rfl, rfl, ?_⟩
  · rfl
  · simp [ledgerEnv, ledgerClaimA, Claim.triple, ledgerHash, ledgerTripleA]

/-- A prover that accepts every query. -/
private def ledgerAnyEnv : Env := ⟨ledgerHash, fun _ => True⟩

theorem SoundProverLoadBearing : Properties.SoundProverLoadBearing := by
  have r := Reach.step (Reach.step (ledger_reach_configured _ ledgerAnyEnv)
    (ledger_step_deposit Checks.source ledgerAnyEnv _ ledgerTripleB 13 rfl rfl rfl (fun _ => rfl)))
    (Step.recover (cl := ledgerClaimB) ledger_ext12
      ⟨rfl, fun _ => trivial, fun _ => by
        simp [ledgerDeposit, afterWrite, setSlot, ledgerConfigured, ledgerAnyEnv, ledgerClaimB,
          Claim.asFailure, Claim.triple, ledgerTripleB], fun _ => rfl⟩)
  refine ⟨ledgerAnyEnv, ledgerCfg, ledgerFresh, _, ledgerTruth, rfl, r, ledgerClaimB.asFailure, 2,
    ?_, ?_, rfl, trivial⟩
  · simp [afterClaim, ledgerDeposit, afterWrite, ledgerConfigured]
  · simp [ledgerTruth, ledgerClaimB, Claim.asFailure]

theorem RouterConfiguredLoadBearing : Properties.RouterConfiguredLoadBearing := by
  -- `initialize(10)`, then `setL1AssetRouter(20)`: an outside address, not the router `2`.
  let sOut : Sys := ⟨⟨true, 10, 0, false, fun _ _ => 0, 20, 0, 0, ledgerZeroDeprecated⟩, false, []⟩
  have r0 : Reach Checks.source ledgerEnv ledgerCfg ledgerFresh sOut :=
    .step (.step (.refl _) (Step.initialize ledger_ext10 rfl (by decide)))
      (Step.setL1AssetRouter ledger_ext10 rfl rfl (by decide))
  have r1 := Reach.step r0 (Step.forwarded (c := 5) (v := 7) (h := 9) ledger_ext20 rfl rfl
    (fun _ => rfl))
  have r2 := Reach.step r1 (Step.recover (cl := ledgerClaimA) ledger_ext10
    ⟨rfl, fun _ => by simp [ledgerEnv, ledgerTruth, ledgerClaimA, Claim.asFailure, Claim.query],
      fun _ => by
        simp [afterWrite, ledgerEnv, ledgerClaimA, Claim.asFailure, Claim.triple, sOut,
          ledgerTripleA, ledgerHash],
      fun h => absurd h (by decide)⟩)
  refine ⟨ledgerEnv, ledgerCfg, ledgerFresh, _, rfl, fun _ _ => rfl, r2, ?_, ?_,
    ⟨5, 9, 7, ?_, by decide⟩, ledgerClaimA.asFailure, 20, ?_, ?_⟩
  · simp only [RouterConfigured, afterClaim, afterWrite, sOut, ledgerCfg]
    decide
  · intro t c h v hm
    simp [afterClaim, afterWrite, sOut] at hm
  · simp [afterClaim, afterWrite, sOut]
  · simp [afterClaim, afterWrite, sOut]
  · simp [ledgerEnv, ledgerClaimA, Claim.asFailure, Claim.triple, ledgerHash, ledgerTripleA]

/-- A hash sending A to `0`. -/
private def ledgerZeroEnv : Env :=
  ⟨fun t => if t = ledgerTripleA then 0 else 7, fun q => ledgerTruth q.chainId q.l2TxHash = some q.status⟩

theorem ZeroHashClaimClearsEmptySlot : Properties.ZeroHashClaimClearsEmptySlot := by
  have ok : ∀ s : Sys, s.n.paused = false → s.routerPaused = false → s.n.depositHappened 5 9 = 0 →
      ClaimOk Checks.source ledgerZeroEnv ledgerCfg s ledgerClaimA.asFailure :=
    fun s hp hr hd => ⟨hp, fun _ => by
      simp [ledgerZeroEnv, ledgerTruth, ledgerClaimA, Claim.asFailure, Claim.query],
      fun _ => by
        simp only [ledgerClaimA, Claim.asFailure, Claim.triple, ledgerZeroEnv]
        rw [hd]; simp [ledgerTripleA],
      fun _ => hr⟩
  have r := Reach.step (Reach.step (ledger_reach_configured Checks.source ledgerZeroEnv)
    (Step.recover (cl := ledgerClaimA) ledger_ext10 (ok _ rfl rfl rfl)))
    (Step.recover (cl := ledgerClaimA) ledger_ext10 (ok _ rfl rfl (by
      simp [afterClaim, setSlot, ledgerConfigured])))
  refine ⟨ledgerZeroEnv, ledgerCfg, ledgerFresh, _, 5, 9, rfl, fun _ _ => rfl, r, ?_, ?_, ?_, ?_, ?_⟩
  · exact Or.inr (by simp [afterClaim, ledgerConfigured, ledgerCfg])
  · intro o c h v hm
    simp [afterClaim, ledgerConfigured] at hm
  · simp [afterClaim, ledgerConfigured, isNzWrite, occupied, ledgerFresh]
  · simp [afterClaim, ledgerConfigured, isClear, ledgerClaimA, Claim.asFailure]
  · simp [afterClaim, ledgerConfigured, isZeroClear, ledgerZeroEnv, ledgerClaimA, Claim.asFailure,
      Claim.triple, ledgerTripleA]

theorem RepeatedKeyAccepted : Properties.RepeatedKeyAccepted := by
  refine ⟨ledgerEnv, ledgerCfg, ledgerConfigured, _, _, 10, 12, 5, 9, 11, [2],
    Step.twoBridges rfl rfl rfl (fun _ => rfl), Step.twoBridges rfl rfl rfl ?_, ?_, ?_, ?_⟩
  · intro _
    simp [afterWrite, SecondBridge.hash, setSlot, ledgerConfigured]
  · simp [afterWrite, SecondBridge.hash, setSlot, ledgerConfigured]
  · simp [afterWrite, SecondBridge.hash, SecondBridge.origin]
  · simp [ledgerEnv, ledgerHash, ledgerTripleA, ledgerTripleB]

theorem RecordLeavesOnlyByPreimageWitness : Properties.RecordLeavesOnlyByPreimageWitness := by
  refine ⟨ledgerEnv, ledgerCfg, ledgerOneDeposit ledgerEnv, _, ledgerClaimA,
    .step (.refl _) (Step.confirm (cl := ledgerClaimA) ledger_ext10
      ⟨rfl, fun _ => by simp [ledgerEnv, ledgerTruth, ledgerClaimA, Claim.query], fun _ => ?_,
        fun _ => rfl⟩), ?_, ?_, ?_, rfl⟩
  · simp [ledgerOneDeposit, ledgerDeposit, afterWrite, ledgerClaimA, Claim.triple, ledgerTripleA]
  · simp [ledgerOneDeposit, ledgerDeposit, afterWrite, ledgerClaimA, Claim.triple, ledgerTripleA]
  · simp [ledgerEnv, ledgerClaimA, Claim.triple, ledgerHash, ledgerTripleA]
  · simp [afterClaim, ledgerClaimA]

theorem UnclaimedDepositRecoverableWitness : Properties.UnclaimedDepositRecoverableWitness := by
  -- Deposit A, deposit B, B's confirmation; A stays unclaimed and `12` recovers it for `10`.
  have r := Reach.step ledger_reach_two_deposits (Step.confirm ledger_ext12 (ledger_claimB_ok _ rfl rfl
    (by simp [ledgerTwoDeposits, ledgerDeposit, afterWrite, setSlot, ledgerEnv, ledgerHash_B])))
  refine ⟨ledgerEnv, ledgerCfg, ledgerFresh, _, [], _, ledgerTripleA, 5, 9, 12, ledgerClaimA,
    rfl, fun _ _ => rfl, r, rfl, ?_, ?_, rfl, rfl, rfl, rfl, ledger_ext12, by decide, rfl, rfl, rfl, ?_⟩
  · simp [ledgerEnv, ledgerHash_A]
  · simp [isClear, ledgerClaimB]
  · simp [ledgerEnv, ledgerTruth, ledgerClaimA, Claim.asFailure, Claim.query]

theorem LedgerStepWitness : Properties.LedgerStepWitness := by
  let s₂ := ledgerOneDeposit ledgerEnv
  let s₃ : Sys := { s₂ with n := { s₂.n with paused := true } }
  let s₄ : Sys := { s₃ with n := { s₃.n with paused := false } }
  have hd : s₄.n.depositHappened 5 9 = 7 := by
    simp [s₄, s₃, s₂, ledgerOneDeposit, ledgerDeposit, afterWrite, ledgerEnv, ledgerHash_A]
  refine ⟨ledgerEnv, ledgerCfg, ledgerConfigured, s₂, s₃, s₄, afterClaim s₄ ledgerClaimA.asFailure, _,
    10, 10, 5, 11, [1], 9, ledgerClaimA,
    ledger_step_deposit _ _ _ ledgerTripleA 9 rfl rfl rfl (fun _ => rfl), ?_,
    Step.pause ledger_ext10 rfl rfl,
    by simp [s₃, s₂, ledgerOneDeposit, ledgerDeposit, afterWrite, ledgerConfigured], Step.unpause ledger_ext10 rfl rfl, rfl, ?_,
    by simp [s₄, s₃], Step.recover ledger_ext10 (ledger_claimA_ok s₄ rfl rfl hd), rfl, rfl,
    Step.renounceOwnership ledger_ext10 rfl, ?_⟩
  · simp [s₂, ledgerOneDeposit, ledgerDeposit, afterWrite, ledgerEnv, ledgerHash_A]
  · simp [s₃, s₂, ledgerOneDeposit, ledgerDeposit, afterWrite, ledgerEnv, ledgerHash_A]
  · simp [afterClaim, s₄, s₃, s₂, ledgerOneDeposit, ledgerDeposit, afterWrite, ledgerConfigured]

theorem InitializeOnlyOnceWitness : Properties.InitializeOnlyOnceWitness := by
  let s₁ : Sys := ⟨⟨true, 10, 0, false, fun _ _ => 0, 0, 0, 0, ledgerZeroDeprecated⟩, false, []⟩
  have r : Reach Checks.source ledgerEnv ledgerCfg s₁ _ :=
    .step (.step (.step (.refl _) (Step.setL1AssetRouter ledger_ext10 rfl rfl (by decide)))
      (ledger_step_deposit _ ledgerEnv _ ledgerTripleA 9 rfl rfl rfl (fun _ => rfl)))
      (Step.recover (cl := ledgerClaimA) ledger_ext10 (ledger_claimA_ok _ rfl rfl (by
        simp [ledgerDeposit, afterWrite, ledgerEnv, ledgerHash_A])))
  refine ⟨ledgerEnv, ledgerCfg, ledgerFresh, s₁, _, 10, 10, rfl,
    Step.initialize ledger_ext10 rfl (by decide), r, ?_⟩
  simp [afterClaim, ledgerDeposit, afterWrite, s₁]

theorem RouterPausedStepWitness : Properties.RouterPausedStepWitness := by
  let s : Sys := { ledgerOneDeposit ledgerEnv with routerPaused := true }
  refine ⟨ledgerEnv, ledgerCfg, s, _, _, Step.pause ledger_ext10 rfl rfl, rfl, rfl, ⟨5, 9, ?_⟩, ?_⟩
  · simp [s, ledgerOneDeposit, ledgerDeposit, afterWrite, ledgerEnv, ledgerHash_A]
  · simp [s, ledgerOneDeposit, ledgerDeposit, afterWrite, ledgerConfigured]

theorem ConfigSetOnceWitness : Properties.ConfigSetOnceWitness := by
  -- All three addresses set: router `2`, vault `4`, interop handler `6`.
  let sAll : Sys := ⟨⟨true, 10, 0, false, fun _ _ => 0, 2, 4, 6, ledgerZeroDeprecated⟩, false, []⟩
  have r := Reach.step (Reach.step (Reach.refl sAll)
    (ledger_step_deposit Checks.source ledgerEnv sAll ledgerTripleA 9 rfl rfl rfl (fun _ => rfl)))
    (Step.recover (cl := ledgerClaimA) ledger_ext10 (ledger_claimA_ok _ rfl rfl (by
      simp [ledgerDeposit, afterWrite, ledgerEnv, ledgerHash_A, sAll])))
  refine ⟨ledgerEnv, ledgerCfg, sAll, _, r, by decide, by decide, by decide, ?_⟩
  simp [afterClaim, ledgerDeposit, afterWrite, sAll]

end Contracts.L1Nullifier
