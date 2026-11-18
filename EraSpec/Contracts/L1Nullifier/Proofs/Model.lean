import EraSpec.Contracts.L1Nullifier.Properties.Model

/-!
# Proofs: the nullifier's deposit ledger

Every run-level result is an induction over `Reach` with a one-step lemma that does a case split
over all fifteen `Step` constructors. The ledger results rest on two one-step facts: a write needs
an empty slot (`DepositExists`) and a clear needs the slot to equal the claimed hash
(`DepositDoesNotExist`). The countermodels and witnesses are concrete runs from fresh storage.
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

theorem RefundGoesToDepositor : Properties.RefundGoesToDepositor := by
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

/-! ## Configuration and legacy -/

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

/-! ## Concrete worlds -/

private def zeroDeprecated : Deprecated :=
  ⟨0, 0, 0, 0, 0, fun _ => 0, fun _ _ _ => false, fun _ => false, fun _ _ => 0, 0, 0⟩

/-- Fresh proxy storage: everything zero, not initialized. -/
private def freshSys : Sys :=
  ⟨⟨false, 0, 0, false, fun _ _ => 0, 0, 0, 0, zeroDeprecated⟩, false, []⟩

/-- Nullifier `1`, router `2`, bridgehub `3`. -/
private def wCfg : Cfg := ⟨1, 2, 3⟩

/-- A claim of transaction `9` on chain `5` by sender `10` for asset `11`, empty data. -/
private def wClaim : Claim := ⟨5, 10, 0, .failure, 11, [], 9, 0, 0, []⟩

private lemma ext10 : ExternalSender wCfg 10 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

private lemma ne10 : (10 : UInt256) ≠ 0 := by decide
private lemma ne2 : (2 : UInt256) ≠ 0 := by decide
private lemma ne7 : (7 : UInt256) ≠ 0 := by decide

/-- A prover accepting exactly the failure claims, sound for "every transaction failed". -/
private def failEnv : Env := ⟨fun _ => 7, fun q => q.status = .failure⟩

/-- Storage after `initialize(10)` and `setL1AssetRouter(2)`. -/
private def s2 : Sys := ⟨⟨true, 10, 0, false, fun _ _ => 0, 2, 0, 0, zeroDeprecated⟩, false, []⟩

/-- Fresh storage, initialized by `10`, router configured, deposit of `wClaim.triple` at `(5, 9)`. -/
private lemma run_deposit (chk : Checks) (env : Env) :
    Reach chk env wCfg freshSys
      (afterWrite s2 (.deposit wClaim.triple) 5 9 (env.txDataHash wClaim.triple)) := by
  have r : Reach chk env wCfg freshSys s2 :=
    .step (.step (.refl _) (Step.initialize ext10 rfl ne10)) (Step.setL1AssetRouter ext10 rfl rfl ne2)
  exact .step r (Step.twoBridges (caller := 10) (req := .deposit 11 []) rfl rfl rfl (fun _ => rfl))

theorem LifecycleWitness : Properties.LifecycleWitness := by
  have r := run_deposit Checks.source failEnv
  have r2 := Reach.step r (Step.recover (cl := wClaim) ext10
    ⟨rfl, fun _ => rfl, fun _ => by simp [afterWrite, Claim.asFailure, Claim.triple, wClaim, s2], fun _ => rfl⟩)
  refine ⟨failEnv, wCfg, freshSys, _, fun _ _ => some .failure, ?_, rfl, rfl, fun _ _ => rfl, r2,
    Or.inr rfl, wClaim.asFailure, 2, ?_, rfl, rfl, ne7, ?_⟩
  · intro q hq; simp only [failEnv] at hq; rw [hq]
  · simp [afterClaim, afterWrite, s2, wClaim, Claim.triple, Claim.asFailure]
  · simp [afterClaim, afterWrite, Claim.asFailure, Claim.triple, failEnv, s2, wClaim]

theorem PausedOwnerlessReachable : Properties.PausedOwnerlessReachable := by
  have r := run_deposit Checks.source failEnv
  have r2 := Reach.step (Reach.step r (Step.pause ext10 rfl rfl)) (Step.renounceOwnership ext10 rfl)
  refine ⟨failEnv, wCfg, freshSys, _, rfl, rfl, r2, rfl, rfl, rfl, rfl, 5, 9, ?_⟩
  simp [afterWrite, failEnv, ne7, s2, wClaim, Claim.triple]

theorem HashCheckLoadBearing : Properties.HashCheckLoadBearing := by
  have r := run_deposit { Checks.source with dataHash := false } failEnv
  have ok : ∀ s : Sys, s.n.paused = false → s.routerPaused = false →
      ClaimOk { Checks.source with dataHash := false } failEnv wCfg s wClaim.asFailure :=
    fun s hp hr => ⟨hp, fun _ => rfl, fun h => absurd h (by decide), fun _ => hr⟩
  have r2 := Reach.step r (Step.recover (cl := wClaim) ext10 (ok _ rfl rfl))
  have r3 := Reach.step r2 (Step.recover (cl := wClaim) ext10 (ok _ rfl rfl))
  refine ⟨failEnv, wCfg, freshSys, _, 5, 9, rfl, r3, ?_, ?_, ?_⟩
  · simp [afterClaim, afterWrite, isNzWrite, occupied, freshSys, failEnv, ne7, s2, wClaim,
      Claim.triple, Claim.asFailure]
  · simp [afterClaim, afterWrite, isZeroClear, failEnv, ne7, s2, wClaim, Claim.triple,
      Claim.asFailure]
  · simp [afterClaim, afterWrite, isClear, Claim.asFailure, wClaim, s2, Claim.triple]

/-- A prover accepting exactly the success claims, sound for "every transaction succeeded". -/
private def succEnv : Env := ⟨fun _ => 7, fun q => q.status = .success⟩

theorem ProofCheckLoadBearing : Properties.ProofCheckLoadBearing := by
  have r := run_deposit { Checks.source with proof := false } succEnv
  have r2 := Reach.step r (Step.recover (cl := wClaim) ext10
    ⟨rfl, fun h => absurd h (by decide),
      fun _ => by simp [afterWrite, Claim.asFailure, Claim.triple, wClaim, s2], fun _ => rfl⟩)
  refine ⟨succEnv, wCfg, freshSys, _, fun _ _ => some .success, ?_, rfl, r2, wClaim.asFailure, 2,
    ?_, rfl, rfl⟩
  · intro q hq; simp only [succEnv] at hq; rw [hq]
  · simp [afterClaim, afterWrite, s2, wClaim, Claim.triple, Claim.asFailure]

/-- Hash = the sender, so two deposits by different senders record different values. -/
private def senderEnv : Env := ⟨fun t => t.sender, fun _ => True⟩

theorem DepositExistsLoadBearing : Properties.DepositExistsLoadBearing := by
  have r := run_deposit { Checks.source with depositExists := false } senderEnv
  have r2 := Reach.step r (Step.twoBridges (caller := 12) (c := 5) (h := 9) (req := .deposit 11 [])
    (chk := { Checks.source with depositExists := false }) rfl rfl rfl (fun h => absurd h (by decide)))
  refine ⟨senderEnv, wCfg, freshSys, _, 5, 9, rfl, r2, ?_⟩
  simp [afterWrite, isClear, isNzWrite, isZeroClear, occupied, senderEnv, SecondBridge.origin,
    SecondBridge.hash, Claim.triple, wClaim, freshSys, s2]

theorem OnlyNullifierLoadBearing : Properties.OnlyNullifierLoadBearing := by
  have r := Reach.step (Reach.refl freshSys)
    (Step.routerConfirm (chk := { Checks.source with onlyNullifier := false }) (env := failEnv)
      (c := 5) (st := .failure) (t := wClaim.triple) ext10 (fun h => absurd h (by decide)) rfl)
  refine ⟨failEnv, wCfg, freshSys, _, rfl, r, ?_, fun c h => ?_⟩
  · simp [freshSys, isHandler, wClaim, Claim.triple]
  · simp [freshSys, isClear, wClaim, Claim.triple]

theorem RepeatedKeyAccepted : Properties.RepeatedKeyAccepted := by
  let s : Sys := { freshSys with n := { freshSys.n with l1AssetRouter := 2 } }
  refine ⟨failEnv, wCfg, s, _, _, 10, 10, 5, 9, .counterpart, .counterpart,
    Step.twoBridges rfl rfl rfl (fun _ => rfl), Step.twoBridges rfl rfl rfl ?_⟩
  intro _
  simp [afterWrite, SecondBridge.hash, s]

end Contracts.L1Nullifier
