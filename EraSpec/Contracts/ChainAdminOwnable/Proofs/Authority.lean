import EraSpec.Contracts.ChainAdminOwnable.Properties.Authority

/-!
# Proofs: who drives the calls of `ChainAdminOwnable`, and what a renounce leaves

* `sem_events_ok`: one induction over `Sem` for the call and write checks.
* `sem_recv`: every diamond or Bridgehub entry from the `ChainAdminOwnable` is matched by a
  logged call it made, except the entry of the call a derivation itself describes.
* `sem_logged`: the storage-value results, generic in the value read and in the event that
  accounts for a change.
* `sem_zeroSetter`: a zero setter stays zero and makes no call while no setter write is logged.
* `sem_renounced`: from renounced storage, the storage; for every diamond that the
  `ChainAdminOwnable` holds with no nomination and that is not cut, its admin pair and which of its
  admin-gated functions can succeed; and the shape of every event. It is used again in
  `Proofs/AdminRoles.lean`.
* `sem_ownerless`: runs keep "owner zero implies nominee zero".
-/

namespace Contracts.ChainAdminOwnable

/-! ## State setters -/

@[simp] lemma State.setCao_cao (S : State) (σ : CaoState) : (S.setCao σ).cao = σ := rfl
@[simp] lemma State.setCao_chain (S : State) (σ : CaoState) : (S.setCao σ).chain = S.chain := rfl
@[simp] lemma State.setCao_hub (S : State) (σ : CaoState) : (S.setCao σ).hub = S.hub := rfl
@[simp] lemma State.setChain_cao (S : State) (d : Address) (p : AdminPair) :
    (S.setChain d p).cao = S.cao := rfl
@[simp] lemma State.setChain_hub (S : State) (d : Address) (p : AdminPair) :
    (S.setChain d p).hub = S.hub := rfl
lemma State.setChain_chain (S : State) (d x : Address) (p : AdminPair) :
    (S.setChain d p).chain x = if x = d then p else S.chain x := rfl
@[simp] lemma State.setHub_cao (S : State) (h : HubState) : (S.setHub h).cao = S.cao := rfl
@[simp] lemma State.setHub_chain (S : State) (h : HubState) : (S.setHub h).chain = S.chain := rfl
@[simp] lemma State.setHub_hub (S : State) (h : HubState) : (S.setHub h).hub = h := rfl

/-! ## The setter's calldata -/

lemma multiplierData_take (n d : ℕ) : (multiplierData n d).take 4 = SEL_SET_MULTIPLIER := by
  simp [multiplierData, SEL_SET_MULTIPLIER]

/-- The setter's calldata selects no `Ownable2Step` writer. -/
lemma decodeOwnOp_multiplierData (abi : Abi) (n d : ℕ) :
    decodeOwnOp abi (multiplierData n d) = none := by
  have h1 : SEL_SET_MULTIPLIER ≠ SEL_TRANSFER_OWNERSHIP := by decide
  have h2 : SEL_SET_MULTIPLIER ≠ SEL_ACCEPT_OWNERSHIP := by decide
  have h3 : SEL_SET_MULTIPLIER ≠ SEL_RENOUNCE_OWNERSHIP := by decide
  simp [decodeOwnOp, multiplierData_take, h1, h2, h3]

/-- The setter's calldata selects neither `setPendingAdmin` nor `acceptAdmin`. -/
lemma decodeAdminOp_multiplierData (abi : Abi) (n d : ℕ) :
    decodeAdminOp abi (multiplierData n d) = none := by
  have h1 : SEL_SET_MULTIPLIER ≠ SEL_SET_PENDING_ADMIN := by decide
  have h2 : SEL_SET_MULTIPLIER ≠ SEL_ACCEPT_ADMIN := by decide
  simp [decodeAdminOp, multiplierData_take, h1, h2]

lemma setMultiplier_not_bridgehub : SEL_SET_MULTIPLIER ∉ BRIDGEHUB_SELECTORS := by decide

/-- `ownStep` from an ownerless state with no nominee succeeds only for the zero address. -/
lemma ownStep_ownerless {s : Address} {op : OwnOp} {o p : Address}
    (h : ownStep s 0 0 op = some (o, p)) : s = 0 := by
  cases op <;> simp only [ownStep] at h <;> split_ifs at h with hs <;> exact hs

/-! ## Calls and writes -/

/-- What a judgement may assume about how it was entered: a `multicall` loop was entered by the
owner of the storage it records. -/
private def AuthPre : Judgement → Prop
  | .loop inv pre _ _ _ => inv = pre.owner
  | _ => True

/-- A logged call is authorized by its origin; a logged write passed its guard. -/
private def EventChecked : Event → Prop
  | .caoCall o c _ => o.Authorized c
  | .caoWrite inv pre w => w.Guard inv pre
  | _ => True

private lemma eventChecked_of_ownStep {s : Address} {σ : CaoState} {op : OwnOp} {o p : Address}
    (h : ownStep s σ.owner σ.pending op = some (o, p)) :
    EventChecked (.caoWrite s σ (.own op)) := by
  cases op <;> simp only [ownStep] at h <;> split_ifs at h with hs <;> cases h <;> exact hs

private theorem sem_events_ok {cfg : Config} {j : Judgement} {S S' : State} {L : List Event}
    (h : Sem cfg j S L S') : AuthPre j → ∀ e ∈ L, EventChecked e := by
  induction h with
  | callFails => intro _ e he; simp at he
  | caoReceive => intro _ e he; simp at he
  | caoView => intro _ e he; simp at he
  | caoOwn _ _ _ hstep =>
      intro _ e he
      rw [List.mem_singleton] at he
      subst he
      exact eventChecked_of_ownStep hstep
  | caoSetSetter _ _ _ _ hown =>
      intro _ e he
      rw [List.mem_singleton] at he
      subst he
      exact hown
  | caoMulticall _ _ _ hown _ _ ih => intro _; exact ih hown
  | caoSetMultiplier _ _ _ _ hset _ ih =>
      intro _ e he
      rcases List.mem_append.mp he with he | he
      · exact ih trivial e he
      · rw [List.mem_singleton] at he
        subst he
        exact ⟨hset, rfl⟩
  | chainAdmin => intro _ e he; rw [List.mem_singleton] at he; subst he; trivial
  | chainGated _ _ _ _ ih =>
      intro _ e he
      rcases List.mem_cons.mp he with he | he
      · subst he; trivial
      exact ih trivial e he
  | chainCut _ _ _ _ ih =>
      intro _ e he
      rcases List.mem_cons.mp he with he | he
      · subst he; trivial
      rcases List.mem_cons.mp he with he | he
      · subst he; trivial
      exact ih trivial e he
  | chainOther _ _ _ ih =>
      intro _ e he
      rcases List.mem_cons.mp he with he | he
      · subst he; trivial
      exact ih trivial e he
  | hubOwn => intro _ e he; rw [List.mem_singleton] at he; subst he; trivial
  | hubAdmin => intro _ e he; rw [List.mem_singleton] at he; subst he; trivial
  | hubOther _ _ _ _ _ ih =>
      intro _ e he
      rcases List.mem_cons.mp he with he | he
      · subst he; trivial
      exact ih trivial e he
  | external _ _ _ _ ih => intro _; exact ih trivial
  | loopDone => intro _ e he; simp at he
  | loopStep hc _ _ _ ih1 ih2 =>
      intro hpre e he
      rcases List.mem_append.mp he with he | he
      · exact ih1 trivial e he
      rcases List.mem_cons.mp he with he | he
      · subst he
        exact ⟨hpre, hc⟩
      · exact ih2 hpre e he
  | actsNil => intro _ e he; simp at he
  | actsCall _ _ _ _ ih1 ih2 =>
      intro _ e he
      rcases List.mem_append.mp he with he | he
      · exact ih1 trivial e he
      · exact ih2 trivial e he

theorem CallsAreOwnersOrSetters : Properties.CallsAreOwnersOrSetters := by
  intro cfg S S' L h o c ok hm
  exact sem_events_ok h trivial _ hm

theorem WritesAreGuarded : Properties.WritesAreGuarded := by
  intro cfg S S' L h inv pre w hm
  exact sem_events_ok h trivial _ hm

/-! ## What the receiving contracts see -/

/-- `e` is the entry that a successful call `c` by the `ChainAdminOwnable` leaves in a diamond or
in the Bridgehub. -/
private def EntryOf (cfg : Config) (c : Call) (e : Event) : Prop :=
  e = .chainEntry c.target cfg.cao (c.data.take 4) ∨
    (c.target = cfg.hub ∧ e = .hubEntry cfg.cao (c.data.take 4))

/-- An entry whose `msg.sender` is the `ChainAdminOwnable`. -/
private def FromCao (cfg : Config) : Event → Prop
  | .chainEntry _ s _ => s = cfg.cao
  | .hubEntry s _ => s = cfg.cao
  | _ => False

/-- A logged successful call of the `ChainAdminOwnable` left `e`. -/
private def Matched (cfg : Config) (L : List Event) (e : Event) : Prop :=
  ∃ o c, Event.caoCall o c true ∈ L ∧ EntryOf cfg c e

private lemma Matched.mono {cfg : Config} {L L' : List Event} {e : Event}
    (h : Matched cfg L e) (hs : ∀ x ∈ L, x ∈ L') : Matched cfg L' e := by
  obtain ⟨o, c, hm, he⟩ := h
  exact ⟨o, c, hs _ hm, he⟩

/-- Every entry from the `ChainAdminOwnable` in a derivation's log is matched in that log, except,
for a call by the `ChainAdminOwnable` itself, the entry that very call leaves. -/
private def Recv (cfg : Config) : Judgement → List Event → Prop
  | .call s c ok, L => ∀ e ∈ L, FromCao cfg e →
      Matched cfg L e ∨ (s = cfg.cao ∧ ok = true ∧ EntryOf cfg c e)
  | .loop _ _ _ _ _, L => ∀ e ∈ L, FromCao cfg e → Matched cfg L e
  | .acts, L => ∀ e ∈ L, FromCao cfg e → Matched cfg L e

private theorem sem_recv {cfg : Config} {j : Judgement} {S S' : State} {L : List Event}
    (h : Sem cfg j S L S') : Recv cfg j L := by
  induction h with
  | callFails => intro e he; simp at he
  | caoReceive => intro e he; simp at he
  | caoView => intro e he; simp at he
  | caoOwn => intro e he hf; rw [List.mem_singleton] at he; subst he; exact hf.elim
  | caoSetSetter => intro e he hf; rw [List.mem_singleton] at he; subst he; exact hf.elim
  | caoMulticall _ _ _ _ _ _ ih => intro e he hf; exact Or.inl (ih e he hf)
  | caoSetMultiplier _ _ _ _ _ _ ih =>
      intro e he hf
      left
      rcases List.mem_append.mp he with he | he
      · rcases ih e he hf with hm | ⟨-, -, hent⟩
        · exact hm.mono fun x hx => List.mem_append_left _ hx
        · exact ⟨_, _, List.mem_append_right _ (List.mem_singleton_self _), hent⟩
      · rw [List.mem_singleton] at he
        subst he
        exact hf.elim
  | @chainAdmin s c S op p _ _ _ _ =>
      intro e he hf
      rw [List.mem_singleton] at he
      subst he
      exact Or.inr ⟨hf, rfl, Or.inl (by rw [show s = cfg.cao from hf])⟩
  | @chainGated s c S S' L _ _ _ _ ih =>
      intro e he hf
      rcases List.mem_cons.mp he with he | he
      · subst he
        exact Or.inr ⟨hf, rfl, Or.inl (by rw [show s = cfg.cao from hf])⟩
      · exact Or.inl ((ih e he hf).mono fun x hx => by simp [hx])
  | @chainCut s c S S' L p _ _ _ _ ih =>
      intro e he hf
      rcases List.mem_cons.mp he with he | he
      · subst he
        exact Or.inr ⟨hf, rfl, Or.inl (by rw [show s = cfg.cao from hf])⟩
      rcases List.mem_cons.mp he with he | he
      · subst he; exact hf.elim
      · exact Or.inl ((ih e he hf).mono fun x hx => by simp [hx])
  | @chainOther s c S S' L _ _ _ ih =>
      intro e he hf
      rcases List.mem_cons.mp he with he | he
      · subst he
        exact Or.inr ⟨hf, rfl, Or.inl (by rw [show s = cfg.cao from hf])⟩
      · exact Or.inl ((ih e he hf).mono fun x hx => by simp [hx])
  | @hubOwn s c S op o p ht _ _ _ _ =>
      intro e he hf
      rw [List.mem_singleton] at he
      subst he
      exact Or.inr ⟨hf, rfl, Or.inr ⟨ht, by rw [show s = cfg.cao from hf]⟩⟩
  | @hubAdmin s c S op hh ht _ _ _ _ =>
      intro e he hf
      rw [List.mem_singleton] at he
      subst he
      exact Or.inr ⟨hf, rfl, Or.inr ⟨ht, by rw [show s = cfg.cao from hf]⟩⟩
  | @hubOther s c S S' L ht _ _ _ _ ih =>
      intro e he hf
      rcases List.mem_cons.mp he with he | he
      · subst he
        exact Or.inr ⟨hf, rfl, Or.inr ⟨ht, by rw [show s = cfg.cao from hf]⟩⟩
      · exact Or.inl ((ih e he hf).mono fun x hx => by simp [hx])
  | external _ _ _ _ ih => intro e he hf; exact Or.inl (ih e he hf)
  | loopDone => intro e he; simp at he
  | @loopStep inv pre rs ok cs i c S S1 S2 L1 L2 _ _ _ _ ih1 ih2 =>
      intro e he hf
      rcases List.mem_append.mp he with he | he
      · rcases ih1 e he hf with hm | ⟨-, hok, hent⟩
        · exact hm.mono fun x hx => List.mem_append_left _ hx
        · subst hok
          exact ⟨_, _, List.mem_append_right _ (List.mem_cons_self ..), hent⟩
      rcases List.mem_cons.mp he with he | he
      · subst he; exact hf.elim
      · exact (ih2 e he hf).mono fun x hx => List.mem_append_right _ (List.mem_cons_of_mem _ hx)
  | actsNil => intro e he; simp at he
  | actsCall hsc _ _ _ ih1 ih2 =>
      intro e he hf
      rcases List.mem_append.mp he with he | he
      · rcases ih1 e he hf with hm | ⟨hs, -, -⟩
        · exact hm.mono fun x hx => List.mem_append_left _ hx
        · exact absurd hs hsc
      · exact (ih2 e he hf).mono fun x hx => List.mem_append_right _ hx

theorem ReceivedCallsAreOwnersOrSetters : Properties.ReceivedCallsAreOwnersOrSetters := by
  intro cfg S S' L h
  have hr : Recv cfg .acts L := sem_recv h
  refine ⟨fun D sel hm => ?_, fun sel hm => ?_⟩
  · obtain ⟨o, c, hc, hent⟩ := hr _ hm rfl
    rcases hent with hent | ⟨_, hent⟩
    · simp only [Event.chainEntry.injEq] at hent
      obtain ⟨rfl, -, rfl⟩ := hent
      exact ⟨o, c, hc, sem_events_ok h trivial _ hc, rfl, rfl⟩
    · cases hent
  · obtain ⟨o, c, hc, hent⟩ := hr _ hm rfl
    rcases hent with hent | ⟨ht, hent⟩
    · cases hent
    · simp only [Event.hubEntry.injEq] at hent
      obtain ⟨-, rfl⟩ := hent
      exact ⟨o, c, hc, sem_events_ok h trivial _ hc, ht, rfl⟩

/-! ## A zero setter -/

/-- What a judgement may assume for the sender-based invariants: a call has a nonzero sender. -/
private def NonzeroSender : Judgement → Prop
  | .call s _ _ => s ≠ 0
  | _ => True

private theorem sem_zeroSetter {cfg : Config} (hwf : cfg.WF) {j : Judgement} {S S' : State}
    {L : List Event} (h : Sem cfg j S L S') :
    NonzeroSender j → S.cao.setter = 0 →
      (∀ inv pre x, Event.caoWrite inv pre (.setSetter x) ∉ L) →
      S'.cao.setter = 0 ∧ ∀ inv pre t n d c ok, Event.caoCall (.multiplier inv pre t n d) c ok ∉ L := by
  have hcao0 : cfg.cao ≠ 0 := hwf.1
  induction h with
  | callFails => intro _ h0 _; exact ⟨h0, by simp⟩
  | caoReceive => intro _ h0 _; exact ⟨h0, by simp⟩
  | caoView => intro _ h0 _; exact ⟨h0, by simp⟩
  | caoOwn => intro _ h0 _; exact ⟨h0, by simp⟩
  | caoSetSetter => intro _ _ hno; exact absurd (List.mem_singleton_self _) (hno _ _ _)
  | caoMulticall _ _ _ _ _ _ ih => intro _ h0 hno; exact ih trivial h0 hno
  | caoSetMultiplier _ _ _ _ hset _ _ => intro hs h0 _; exact absurd (hset.trans h0) hs
  | chainAdmin => intro _ h0 _; exact ⟨h0, by simp⟩
  | chainGated _ _ _ _ ih =>
      intro _ h0 hno
      obtain ⟨h1, h2⟩ := ih trivial h0 (fun inv pre x hm => hno inv pre x (by simp [hm]))
      exact ⟨h1, fun inv pre t n d c ok hm => h2 inv pre t n d c ok (by simpa using hm)⟩
  | chainCut _ _ _ _ ih =>
      intro _ h0 hno
      obtain ⟨h1, h2⟩ := ih trivial h0 (fun inv pre x hm => hno inv pre x (by simp [hm]))
      exact ⟨h1, fun inv pre t n d c ok hm => h2 inv pre t n d c ok (by simpa using hm)⟩
  | chainOther _ _ _ ih =>
      intro _ h0 hno
      obtain ⟨h1, h2⟩ := ih trivial h0 (fun inv pre x hm => hno inv pre x (by simp [hm]))
      exact ⟨h1, fun inv pre t n d c ok hm => h2 inv pre t n d c ok (by simpa using hm)⟩
  | hubOwn => intro _ h0 _; exact ⟨h0, by simp⟩
  | hubAdmin => intro _ h0 _; exact ⟨h0, by simp⟩
  | hubOther _ _ _ _ _ ih =>
      intro _ h0 hno
      obtain ⟨h1, h2⟩ := ih trivial h0 (fun inv pre x hm => hno inv pre x (by simp [hm]))
      exact ⟨h1, fun inv pre t n d c ok hm => h2 inv pre t n d c ok (by simpa using hm)⟩
  | external _ _ _ _ ih => intro _ h0 hno; exact ih trivial h0 hno
  | loopDone => intro _ h0 _; exact ⟨h0, by simp⟩
  | loopStep _ _ _ _ ih1 ih2 =>
      intro _ h0 hno
      obtain ⟨h1, h1'⟩ := ih1 hcao0 h0 (fun inv pre x hm => hno inv pre x (by simp [hm]))
      obtain ⟨h2, h2'⟩ := ih2 trivial h1 (fun inv pre x hm => hno inv pre x (by simp [hm]))
      refine ⟨h2, fun inv pre t n d c ok hm => ?_⟩
      rcases List.mem_append.mp hm with hm | hm
      · exact h1' inv pre t n d c ok hm
      rcases List.mem_cons.mp hm with hm | hm
      · simp at hm
      · exact h2' inv pre t n d c ok hm
  | actsNil => intro _ h0 _; exact ⟨h0, by simp⟩
  | actsCall _ hs0 _ _ ih1 ih2 =>
      intro _ h0 hno
      obtain ⟨h1, h1'⟩ := ih1 hs0 h0 (fun inv pre x hm => hno inv pre x (by simp [hm]))
      obtain ⟨h2, h2'⟩ := ih2 trivial h1 (fun inv pre x hm => hno inv pre x (by simp [hm]))
      refine ⟨h2, fun inv pre t n d c ok hm => ?_⟩
      rcases List.mem_append.mp hm with hm | hm
      · exact h1' inv pre t n d c ok hm
      · exact h2' inv pre t n d c ok hm

theorem ZeroSetterIsInert : Properties.ZeroSetterIsInert := by
  intro cfg S S' L hwf h0 h hno
  exact sem_zeroSetter hwf h trivial h0 hno

/-! ## Storage values: unchanged, or accounted for by a logged event -/

/-- The value `f` reads from the `ChainAdminOwnable`'s storage at the end is the one at the
start, or an event of the log accounts for it (`Ok`). -/
private def Logged {α : Type} (f : CaoState → α) (Ok : α → Event → Prop) (S S' : State)
    (L : List Event) : Prop :=
  f S'.cao = f S.cao ∨ ∃ e ∈ L, Ok (f S'.cao) e

private lemma Logged.of_eq {α : Type} {f : CaoState → α} {Ok : α → Event → Prop} {S S' : State}
    {L : List Event} (h : S'.cao = S.cao) : Logged f Ok S S' L :=
  Or.inl (by rw [h])

private lemma Logged.mono {α : Type} {f : CaoState → α} {Ok : α → Event → Prop} {S S' : State}
    {L L' : List Event} (h : Logged f Ok S S' L) (hs : ∀ e ∈ L, e ∈ L') :
    Logged f Ok S S' L' := by
  rcases h with h | ⟨e, he, hok⟩
  · exact Or.inl h
  · exact Or.inr ⟨e, hs e he, hok⟩

private lemma Logged.trans {α : Type} {f : CaoState → α} {Ok : α → Event → Prop}
    {S S1 S2 : State} {L1 L2 : List Event} (h1 : Logged f Ok S S1 L1)
    (h2 : Logged f Ok S1 S2 L2) : Logged f Ok S S2 (L1 ++ L2) := by
  rcases h2 with h2 | ⟨e, he, hok⟩
  · rcases h1 with h1 | ⟨e, he, hok⟩
    · exact Or.inl (h2.trans h1)
    · exact Or.inr ⟨e, List.mem_append_left _ he, by rw [h2]; exact hok⟩
  · exact Or.inr ⟨e, List.mem_append_right _ he, hok⟩

/-- **The storage-value rule.** If each of the two writers either keeps the value `f` reads or
logs an event that accounts for the new value, then so does every derivation. -/
private theorem sem_logged {α : Type} (f : CaoState → α) (Ok : α → Event → Prop)
    (hOwn : ∀ (s : Address) (σ : CaoState) (op : OwnOp) (o p : Address),
      ownStep s σ.owner σ.pending op = some (o, p) →
      f { σ with owner := o, pending := p } = f σ ∨
        Ok (f { σ with owner := o, pending := p }) (.caoWrite s σ (.own op)))
    (hSet : ∀ (s : Address) (σ : CaoState) (x : Address), s = σ.owner →
      f { σ with setter := x } = f σ ∨ Ok (f { σ with setter := x }) (.caoWrite s σ (.setSetter x)))
    {cfg : Config} {j : Judgement} {S S' : State} {L : List Event} (h : Sem cfg j S L S') :
    Logged f Ok S S' L := by
  induction h with
  | callFails => exact Logged.of_eq rfl
  | caoReceive => exact Logged.of_eq rfl
  | caoView => exact Logged.of_eq rfl
  | @caoOwn s c S op o p _ _ _ hstep =>
      rcases hOwn s S.cao op o p hstep with h | h
      · exact Or.inl h
      · exact Or.inr ⟨_, List.mem_singleton_self _, h⟩
  | @caoSetSetter s c S x _ _ _ _ hown =>
      rcases hSet s S.cao x hown with h | h
      · exact Or.inl h
      · exact Or.inr ⟨_, List.mem_singleton_self _, h⟩
  | caoMulticall _ _ _ _ _ _ ih => exact ih
  | caoSetMultiplier _ _ _ _ _ _ ih => exact ih.mono fun e he => List.mem_append_left _ he
  | chainAdmin => exact Logged.of_eq rfl
  | chainGated _ _ _ _ ih => exact ih.mono fun e he => by simp [he]
  | chainCut _ _ _ _ ih => exact ih.mono fun e he => by simp [he]
  | chainOther _ _ _ ih => exact ih.mono fun e he => by simp [he]
  | hubOwn => exact Logged.of_eq rfl
  | hubAdmin => exact Logged.of_eq rfl
  | hubOther _ _ _ _ _ ih => exact ih.mono fun e he => by simp [he]
  | external _ _ _ _ ih => exact ih
  | loopDone => exact Logged.of_eq rfl
  | loopStep _ _ _ _ ih1 ih2 =>
      exact (ih1.trans ih2).mono fun e he => by
        rcases List.mem_append.mp he with he | he <;> simp [he]
  | actsNil => exact Logged.of_eq rfl
  | actsCall _ _ _ _ ih1 ih2 => exact ih1.trans ih2

theorem SetterChangesOnlyByOwner : Properties.SetterChangesOnlyByOwner := by
  intro cfg S S' L h
  have H := sem_logged (fun σ => σ.setter)
    (fun x e => ∃ inv pre, e = .caoWrite inv pre (.setSetter x) ∧ inv = pre.owner)
    (fun _ _ _ _ _ _ => Or.inl rfl)
    (fun s σ x hs => Or.inr ⟨s, σ, rfl, hs⟩) h
  rcases H with H | ⟨e, he, inv, pre, rfl, hinv⟩
  · exact Or.inl H
  · exact Or.inr ⟨inv, pre, he, hinv⟩

theorem OwnerChangesOnlyByAcceptOrRenounce : Properties.OwnerChangesOnlyByAcceptOrRenounce := by
  intro cfg S S' L h
  constructor
  · have H := sem_logged (fun σ => σ.owner)
      (fun x e => (∃ pre, e = .caoWrite x pre (.own .accept) ∧ pre.pending = x) ∨
        (x = 0 ∧ ∃ inv pre, e = .caoWrite inv pre (.own .renounce) ∧ inv = pre.owner))
      (fun s σ op o p hstep => by
        cases op <;> simp only [ownStep] at hstep <;> split_ifs at hstep with hs <;>
          cases hstep
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨σ, rfl, hs.symm⟩)
        · exact Or.inr (Or.inr ⟨rfl, s, σ, rfl, hs⟩))
      (fun _ _ _ _ => Or.inl rfl) h
    rcases H with H | ⟨e, he, ⟨pre, rfl, hp⟩ | ⟨h0, inv, pre, rfl, hinv⟩⟩
    · exact Or.inl H
    · exact Or.inr (Or.inl ⟨pre, he, hp⟩)
    · exact Or.inr (Or.inr ⟨h0, inv, pre, he, hinv⟩)
  · have H := sem_logged (fun σ => σ.pending)
      (fun x e => (x = 0 ∧ ∃ inv pre op, e = .caoWrite inv pre (.own op)) ∨
        ∃ inv pre, e = .caoWrite inv pre (.own (.transfer x)) ∧ inv = pre.owner)
      (fun s σ op o p hstep => by
        cases op <;> simp only [ownStep] at hstep <;> split_ifs at hstep with hs <;>
          cases hstep
        · exact Or.inr (Or.inr ⟨s, σ, rfl, hs⟩)
        · exact Or.inr (Or.inl ⟨rfl, s, σ, _, rfl⟩)
        · exact Or.inr (Or.inl ⟨rfl, s, σ, _, rfl⟩))
      (fun _ _ _ _ => Or.inl rfl) h
    rcases H with H | ⟨e, he, ⟨h0, _⟩ | ⟨inv, pre, rfl, hinv⟩⟩
    · exact Or.inl H
    · exact Or.inr (Or.inl h0)
    · exact Or.inr (Or.inr ⟨inv, pre, he, hinv⟩)

/-! ## From renounced storage -/

/-- What a judgement may assume when it starts from renounced storage: for a call, a nonzero
sender, and the setter's calldata whenever the sender is the `ChainAdminOwnable`. No `multicall`
loop starts from renounced storage. -/
def RenouncedPre (cfg : Config) : Judgement → State → Prop
  | .call s c _, S => S.cao.owner = 0 ∧ S.cao.pending = 0 ∧ s ≠ 0 ∧
      (s = cfg.cao → ∃ t n d, c = ⟨t, 0, multiplierData n d⟩)
  | .loop _ _ _ _ _, _ => False
  | .acts, S => S.cao.owner = 0 ∧ S.cao.pending = 0

/-- The shape of an event of a run from renounced storage `σ`: every call the
`ChainAdminOwnable` makes is a successful `setTokenMultiplier` call for `σ`'s setter, there is no
write to its storage, it enters diamonds only with selector `0x235d9eb5`, and it never enters the
Bridgehub. -/
def RenouncedEventOk (cfg : Config) (σ : CaoState) : Event → Prop
  | .caoCall o c ok =>
      ∃ t n d, o = .multiplier σ.setter σ t n d ∧ c = ⟨t, 0, multiplierData n d⟩ ∧ ok = true
  | .caoWrite _ _ _ => False
  | .chainEntry _ s sel => s = cfg.cao → sel = SEL_SET_MULTIPLIER
  | .cut _ => True
  | .hubEntry s _ => s ≠ cfg.cao

/-- What diamond `D`, held by the renounced `ChainAdminOwnable`, can log: no `setPendingAdmin`,
`acceptAdmin` or `onlyAdmin` function, and an `onlyAdminOrChainTypeManager` function only from
`D`'s chain type manager or as the `ChainAdminOwnable`'s `setTokenMultiplier`. -/
def HeldEntryOk (cfg : Config) (D s : Address) (sel : Bytes) : Prop :=
  sel ∉ SEL_SET_PENDING_ADMIN :: SEL_ACCEPT_ADMIN :: ADMIN_ONLY_SELECTORS ∧
    (sel ∈ ADMIN_OR_CTM_SELECTORS → s = cfg.ctmOf D ∨ (s = cfg.cao ∧ sel = SEL_SET_MULTIPLIER))

/-- What a run from renounced storage keeps: the storage; for every diamond whose admin is the
`ChainAdminOwnable` with no nomination and which the run does not cut, that admin pair and
`HeldEntryOk` for each of its entries; and the shape of each event. -/
def RenouncedPost (cfg : Config) (S S' : State) (L : List Event) : Prop :=
  S'.cao = S.cao ∧
    (∀ D, S.chain D = ⟨cfg.cao, 0⟩ → Event.cut D ∉ L →
      S'.chain D = ⟨cfg.cao, 0⟩ ∧ ∀ s sel, Event.chainEntry D s sel ∈ L → HeldEntryOk cfg D s sel) ∧
    ∀ e ∈ L, RenouncedEventOk cfg S.cao e

lemma RenouncedPost.refl {cfg : Config} {S : State} : RenouncedPost cfg S S [] :=
  ⟨rfl, fun _ h _ => ⟨h, by simp⟩, by simp⟩

/-- Composition of two runs from renounced storage. -/
lemma RenouncedPost.trans {cfg : Config} {S S1 S2 : State} {L1 L2 : List Event}
    (h1 : RenouncedPost cfg S S1 L1) (h2 : RenouncedPost cfg S1 S2 L2) :
    RenouncedPost cfg S S2 (L1 ++ L2) := by
  obtain ⟨c1, d1, e1⟩ := h1
  obtain ⟨c2, d2, e2⟩ := h2
  refine ⟨c2.trans c1, fun D hD hcut => ?_, fun e he => ?_⟩
  · simp only [List.mem_append, not_or] at hcut
    obtain ⟨hD1, g1⟩ := d1 D hD hcut.1
    obtain ⟨hD2, g2⟩ := d2 D hD1 hcut.2
    refine ⟨hD2, fun s sel hm => ?_⟩
    rcases List.mem_append.mp hm with hm | hm
    · exact g1 s sel hm
    · exact g2 s sel hm
  · rcases List.mem_append.mp he with he | he
    · exact e1 e he
    · rw [← c1]; exact e2 e he

/-- A run from renounced storage followed by one event that is neither a cut nor a diamond
entry. -/
lemma RenouncedPost.snoc {cfg : Config} {S S' : State} {L : List Event} {e : Event}
    (h : RenouncedPost cfg S S' L) (he : RenouncedEventOk cfg S.cao e)
    (hcut : ∀ D, e ≠ Event.cut D) (hent : ∀ D s sel, e ≠ Event.chainEntry D s sel) :
    RenouncedPost cfg S S' (L ++ [e]) := by
  obtain ⟨c, d, ev⟩ := h
  refine ⟨c, fun D hD hc => ?_, fun x hx => ?_⟩
  · obtain ⟨hD', g⟩ := d D hD (fun h => hc (List.mem_append_left _ h))
    refine ⟨hD', fun s sel hm => ?_⟩
    rcases List.mem_append.mp hm with hm | hm
    · exact g s sel hm
    · rw [List.mem_singleton] at hm
      exact absurd hm.symm (hent D s sel)
  · rcases List.mem_append.mp hx with hx | hx
    · exact ev x hx
    · rw [List.mem_singleton] at hx
      subst hx
      exact he

/-- A diamond entry in front of a run from renounced storage that starts in the same state. -/
lemma RenouncedPost.consEntry {cfg : Config} {S S' : State} {L : List Event} {T s : Address}
    {sel : Bytes} (h : RenouncedPost cfg S S' L) (hsel : s = cfg.cao → sel = SEL_SET_MULTIPLIER)
    (hheld : S.chain T = ⟨cfg.cao, 0⟩ → HeldEntryOk cfg T s sel) :
    RenouncedPost cfg S S' (.chainEntry T s sel :: L) := by
  obtain ⟨c, d, ev⟩ := h
  refine ⟨c, fun D hD hc => ?_, fun x hx => ?_⟩
  · obtain ⟨hD', g⟩ := d D hD (fun h => hc (List.mem_cons_of_mem _ h))
    refine ⟨hD', fun s' sel' hm => ?_⟩
    rcases List.mem_cons.mp hm with hm | hm
    · simp only [Event.chainEntry.injEq] at hm
      obtain ⟨rfl, rfl, rfl⟩ := hm
      exact hheld hD
    · exact g s' sel' hm
  · rcases List.mem_cons.mp hx with hx | hx
    · subst hx; exact hsel
    · exact ev x hx

lemma setMultiplier_not_adminOnly : SEL_SET_MULTIPLIER ∉ ADMIN_ONLY_SELECTORS := by decide

lemma adminOrCtm_not_dead : ∀ x ∈ ADMIN_OR_CTM_SELECTORS,
    x ∉ SEL_SET_PENDING_ADMIN :: SEL_ACCEPT_ADMIN :: ADMIN_ONLY_SELECTORS := by
  decide

lemma dead_modelled : ∀ x ∈ SEL_SET_PENDING_ADMIN :: SEL_ACCEPT_ADMIN :: ADMIN_ONLY_SELECTORS,
    x ∈ CHAIN_MODELLED_SELECTORS := by
  decide

lemma adminOrCtm_modelled : ∀ x ∈ ADMIN_OR_CTM_SELECTORS, x ∈ CHAIN_MODELLED_SELECTORS := by
  decide

/-- **From renounced storage.** In a well-formed configuration, every derivation whose start
satisfies `RenouncedPre` keeps `RenouncedPost`. -/
theorem sem_renounced {cfg : Config} (hwf : cfg.WF) {j : Judgement} {S S' : State}
    {L : List Event} (h : Sem cfg j S L S') : RenouncedPre cfg j S → RenouncedPost cfg S S' L := by
  obtain ⟨hcao0, hcaoHub, hcaoChain, hhubChain⟩ := hwf
  induction h with
  | callFails => intro _; exact RenouncedPost.refl
  | caoReceive => intro _; exact RenouncedPost.refl
  | caoView => intro _; exact RenouncedPost.refl
  | caoOwn _ _ _ hstep =>
      intro ⟨ho, hp, hs, _⟩
      rw [ho, hp] at hstep
      exact absurd (ownStep_ownerless hstep) hs
  | caoSetSetter _ _ _ _ hown =>
      intro ⟨ho, _, hs, _⟩
      exact absurd (hown.trans ho) hs
  | caoMulticall _ _ _ hown _ _ _ =>
      intro ⟨ho, _, hs, _⟩
      exact absurd (hown.trans ho) hs
  | @caoSetMultiplier s c S S' L t n d _ _ _ _ hset _ ih =>
      intro ⟨ho, hp, _, _⟩
      exact (ih ⟨ho, hp, hcao0, fun _ => ⟨t, n, d, rfl⟩⟩).snoc ⟨t, n, d, by rw [hset], rfl, rfl⟩
        (fun _ h => by cases h) (fun _ _ _ h => by cases h)
  | @chainAdmin s c S op p hch _ hdec hstep =>
      intro ⟨_, _, hs, hcall⟩
      have hsel : s = cfg.cao → c.data.take 4 = SEL_SET_MULTIPLIER := fun hsc => by
        obtain ⟨t, n, d, rfl⟩ := hcall hsc
        exact multiplierData_take n d
      -- A diamond the renounced `ChainAdminOwnable` holds admits neither call.
      have hnot : S.chain c.target ≠ ⟨cfg.cao, 0⟩ := fun hD => by
        cases op with
        | setPending x =>
            simp only [chainAdminStep, hD] at hstep
            split_ifs at hstep with hsa
            obtain ⟨t, n, d, rfl⟩ := hcall hsa
            rw [decodeAdminOp_multiplierData] at hdec
            cases hdec
        | accept =>
            simp only [chainAdminStep, hD] at hstep
            split_ifs at hstep with hsa
            exact hs hsa
      refine ⟨rfl, fun D hD _ => ?_, fun e he => ?_⟩
      · have hDc : D ≠ c.target := fun h => hnot (by rw [← h]; exact hD)
        refine ⟨by simpa [State.setChain_chain, hDc] using hD, fun s' sel' hm => ?_⟩
        rw [List.mem_singleton, Event.chainEntry.injEq] at hm
        exact absurd hm.1 hDc
      · rw [List.mem_singleton] at he
        subst he
        exact hsel
  | @chainGated s c S S' L _ _ hgate _ ih =>
      intro ⟨ho, hp, _, hcall⟩
      have hsel : s = cfg.cao → c.data.take 4 = SEL_SET_MULTIPLIER := fun hsc => by
        obtain ⟨t, n, d, rfl⟩ := hcall hsc
        exact multiplierData_take n d
      refine (ih ⟨ho, hp⟩).consEntry hsel (fun hD => ?_)
      rw [hD] at hgate
      rcases hgate with ⟨hmem, hsa⟩ | ⟨hmem, hsa⟩
      · rw [hsel hsa] at hmem
        exact absurd hmem setMultiplier_not_adminOnly
      · refine ⟨adminOrCtm_not_dead _ hmem, fun _ => ?_⟩
        rcases hsa with hsa | hsa
        · exact Or.inr ⟨hsa, hsel hsa⟩
        · exact Or.inl hsa
  | @chainCut s c S S' L p _ _ _ _ ih =>
      intro ⟨ho, hp, _, hcall⟩
      have hsel : s = cfg.cao → c.data.take 4 = SEL_SET_MULTIPLIER := fun hsc => by
        obtain ⟨t, n, d, rfl⟩ := hcall hsc
        exact multiplierData_take n d
      obtain ⟨hc, hd, he⟩ := ih ⟨ho, hp⟩
      refine ⟨hc, fun D hD hcut => ?_, fun e hm => ?_⟩
      · have hDc : D ≠ c.target := by
          rintro rfl
          exact hcut (by simp)
        have hD' : (S.setChain c.target p).chain D = ⟨cfg.cao, 0⟩ := by
          simpa [State.setChain_chain, hDc] using hD
        obtain ⟨hD2, g⟩ := hd D hD' (fun h => hcut (by simp [h]))
        refine ⟨hD2, fun s' sel' hm => ?_⟩
        rcases List.mem_cons.mp hm with hm | hm
        · simp only [Event.chainEntry.injEq] at hm
          exact absurd hm.1 hDc
        rcases List.mem_cons.mp hm with hm | hm
        · cases hm
        · exact g s' sel' hm
      · rcases List.mem_cons.mp hm with hm | hm
        · subst hm; exact hsel
        rcases List.mem_cons.mp hm with hm | hm
        · subst hm; trivial
        · exact he e hm
  | @chainOther s c S S' L _ hnm _ ih =>
      intro ⟨ho, hp, _, hcall⟩
      have hsel : s = cfg.cao → c.data.take 4 = SEL_SET_MULTIPLIER := fun hsc => by
        obtain ⟨t, n, d, rfl⟩ := hcall hsc
        exact multiplierData_take n d
      exact (ih ⟨ho, hp⟩).consEntry hsel (fun _ =>
        ⟨fun h => hnm (dead_modelled _ h), fun h => absurd (adminOrCtm_modelled _ h) hnm⟩)
  | @hubOwn s c S op o p _ _ _ hdec _ =>
      intro ⟨_, _, _, hcall⟩
      refine ⟨rfl, fun D hD _ => ⟨hD, fun s' sel' hm => by simp at hm⟩, fun e he => ?_⟩
      rw [List.mem_singleton] at he
      subst he
      intro hsc
      obtain ⟨t, n, d, rfl⟩ := hcall hsc
      rw [decodeOwnOp_multiplierData] at hdec
      cases hdec
  | @hubAdmin s c S op hh _ _ _ hdec _ =>
      intro ⟨_, _, _, hcall⟩
      refine ⟨rfl, fun D hD _ => ⟨hD, fun s' sel' hm => by simp at hm⟩, fun e he => ?_⟩
      rw [List.mem_singleton] at he
      subst he
      intro hsc
      obtain ⟨t, n, d, rfl⟩ := hcall hsc
      rw [decodeAdminOp_multiplierData] at hdec
      cases hdec
  | @hubOther s c S S' L _ _ hmem _ _ ih =>
      intro ⟨ho, hp, _, hcall⟩
      obtain ⟨hc, hd, he⟩ := ih ⟨ho, hp⟩
      refine ⟨hc, fun D hD hcut => ?_, fun e hm => ?_⟩
      · obtain ⟨hD2, g⟩ := hd D hD (fun h => hcut (by simp [h]))
        refine ⟨hD2, fun s' sel' hm => ?_⟩
        rcases List.mem_cons.mp hm with hm | hm
        · cases hm
        · exact g s' sel' hm
      · rcases List.mem_cons.mp hm with hm | hm
        · subst hm
          intro hsc
          obtain ⟨t, n, d, rfl⟩ := hcall hsc
          rw [multiplierData_take] at hmem
          exact setMultiplier_not_bridgehub hmem
        · exact he e hm
  | external _ _ _ _ ih =>
      intro ⟨ho, hp, _, _⟩
      exact ih ⟨ho, hp⟩
  | loopDone => intro h; exact h.elim
  | loopStep _ _ _ _ _ _ => intro h; exact h.elim
  | actsNil => intro _; exact RenouncedPost.refl
  | actsCall hsc hs0 _ _ ih1 ih2 =>
      intro ⟨ho, hp⟩
      have H1 := ih1 ⟨ho, hp, hs0, fun h => absurd h hsc⟩
      exact H1.trans (ih2 ⟨H1.1 ▸ ho, H1.1 ▸ hp⟩)

theorem RenounceIsPermanent : Properties.RenounceIsPermanent := by
  intro cfg S S' L hwf ho hp h
  obtain ⟨hc, _, he⟩ := sem_renounced hwf h ⟨ho, hp⟩
  refine ⟨hc, fun inv pre w hw => he _ hw, fun o c ok hm => he _ hm⟩

/-! ## No owner means no nominee -/

private theorem sem_ownerless {cfg : Config} (hwf : cfg.WF) {j : Judgement} {S S' : State}
    {L : List Event} (h : Sem cfg j S L S') :
    NonzeroSender j → (S.cao.owner = 0 → S.cao.pending = 0) →
      (S'.cao.owner = 0 → S'.cao.pending = 0) := by
  have hcao0 : cfg.cao ≠ 0 := hwf.1
  induction h with
  | callFails => intro _ h; exact h
  | caoReceive => intro _ h; exact h
  | caoView => intro _ h; exact h
  | @caoOwn s c S op o p _ _ _ hstep =>
      intro hs hinv
      cases op <;> simp only [ownStep] at hstep <;> split_ifs at hstep with hso <;> cases hstep
      · -- `transferOwnership`: the owner is the nonzero sender and stays
        intro h0
        exact absurd (hso.trans h0) hs
      · -- `acceptOwnership`: the sender becomes the owner
        intro h0
        exact absurd h0 hs
      · intro _; rfl
  | caoSetSetter => intro _ h; exact h
  | caoMulticall _ _ _ _ _ _ ih => intro _ h; exact ih trivial h
  | caoSetMultiplier _ _ _ _ _ _ ih => intro _ h; exact ih hcao0 h
  | chainAdmin => intro _ h; exact h
  | chainGated _ _ _ _ ih => intro _ h; exact ih trivial h
  | chainCut _ _ _ _ ih => intro _ h; exact ih trivial h
  | chainOther _ _ _ ih => intro _ h; exact ih trivial h
  | hubOwn => intro _ h; exact h
  | hubAdmin => intro _ h; exact h
  | hubOther _ _ _ _ _ ih => intro _ h; exact ih trivial h
  | external _ _ _ _ ih => intro _ h; exact ih trivial h
  | loopDone => intro _ h; exact h
  | loopStep _ _ _ _ ih1 ih2 => intro _ h; exact ih2 trivial (ih1 hcao0 h)
  | actsNil => intro _ h; exact h
  | actsCall _ hs0 _ _ ih1 ih2 => intro _ h; exact ih2 trivial (ih1 hs0 h)

theorem OwnerlessHasNoNominee : Properties.OwnerlessHasNoNominee := by
  intro cfg S S' L hwf hinv h
  exact sem_ownerless hwf h trivial hinv

theorem ConstructedThenOwnerlessIsPermanent :
    Properties.ConstructedThenOwnerlessIsPermanent := by
  intro cfg S₀ S₁ S₂ L₁ L₂ o σ hwf hcon h₁ ho h₂
  have hinv₀ : S₀.cao.owner = 0 → S₀.cao.pending = 0 := by
    unfold construct at hcon
    split_ifs at hcon
    intro _
    rw [← Option.some.inj hcon]
  have hp := sem_ownerless hwf h₁ trivial hinv₀ ho
  obtain ⟨hc, _, he⟩ := sem_renounced hwf h₂ ⟨ho, hp⟩
  refine ⟨hc, fun o' c ok hm => ?_⟩
  obtain ⟨t, n, d, h1, h2, _⟩ := he _ hm
  exact ⟨t, n, d, h1, h2⟩

/-! ## Witness runs -/

/-- The witness configuration is well formed. -/
theorem wCfg_wellFormed : wCfg.WF := ⟨by decide, by decide, by decide, by decide⟩

/-- The owner `6` sets the setter to `7`. -/
private theorem w_setSetter {S : State} (ho : S.cao.owner = 6) :
    Sem wCfg (.call 6 ⟨1, 0, withWord SEL_SET_SETTER 7⟩ true) S
      [.caoWrite 6 S.cao (.setSetter 7)] (S.setCao { S.cao with setter := 7 }) :=
  Sem.caoSetSetter (x := 7) rfl rfl (by decide) (by decide) ho.symm

/-- The setter `7` calls `setTokenMultiplier(4, 3, 2)`, which reaches diamond `4`, whose admin is
the `ChainAdminOwnable`. -/
private theorem w_multiplierOnChain {S : State} (hs : S.cao.setter = 7)
    (hadm : (S.chain 4).admin = 1) :
    Sem wCfg (.call 7 ⟨1, 0, viaData 4 3 2⟩ true) S
      ([.chainEntry 4 1 SEL_SET_MULTIPLIER] ++
        [.caoCall (.multiplier 7 S.cao 4 3 2) ⟨4, 0, multiplierData 3 2⟩ true]) S :=
  Sem.caoSetMultiplier (t := 4) (n := 3) (d := 2) rfl rfl (by decide) (by decide) hs.symm
    (Sem.chainGated (by decide) rfl (Or.inr ⟨by decide, Or.inl hadm.symm⟩) Sem.actsNil)

/-- The owner `6`'s `multicall(wCallsA, true)`: the `ChainAdminOwnable` nominates `8` as pending
admin of diamond `4` and of the Bridgehub, from a state where it is the admin of both. -/
private theorem w_multicallA {S : State} (ho : S.cao.owner = 6) (hD : S.chain 4 = ⟨1, 0⟩)
    (hH : S.hub = ⟨9, 0, 1, 0⟩) :
    Sem wCfg (.call 6 ⟨1, 0, SEL_MULTICALL ++ [1]⟩ true) S
      [.chainEntry 4 1 SEL_SET_PENDING_ADMIN,
        .caoCall (.multicall 6 S.cao wCallsA 0) ⟨4, 0, withWord SEL_SET_PENDING_ADMIN 8⟩ true,
        .hubEntry 1 SEL_SET_PENDING_ADMIN,
        .caoCall (.multicall 6 S.cao wCallsA 1) ⟨2, 0, withWord SEL_SET_PENDING_ADMIN 8⟩ true]
      ((S.setChain 4 ⟨1, 8⟩).setHub ⟨9, 0, 1, 8⟩) :=
  Sem.caoMulticall (cs := wCallsA) (rs := true) rfl (by decide) (by decide) ho.symm (by decide)
    (Sem.loopStep (c := ⟨4, 0, withWord SEL_SET_PENDING_ADMIN 8⟩) (ok := true) (by decide)
      (Sem.chainAdmin (op := .setPending 8) (p := ⟨1, 8⟩) (by decide) rfl (by decide)
        (by rw [hD]; decide))
      (fun _ => rfl)
      (Sem.loopStep (c := ⟨2, 0, withWord SEL_SET_PENDING_ADMIN 8⟩) (ok := true) (by decide)
        (Sem.hubAdmin (op := .setPending 8) (h := ⟨9, 0, 1, 8⟩) rfl (by decide) rfl
          (by decide) (by rw [State.setChain_hub, hH]; decide))
        (fun _ => rfl)
        (Sem.loopDone (by decide))))

theorem AuthorityWitness : Properties.AuthorityWitness := by
  refine ⟨by decide, _, _,
    Sem.actsCall (by decide) (by decide) (w_setSetter rfl) <|
    Sem.actsCall (by decide) (by decide) (w_multiplierOnChain rfl rfl) <|
    Sem.actsCall (by decide) (by decide) (w_multicallA rfl rfl rfl) <|
    Sem.actsCall (s := 6) (c := ⟨1, 0, withWord SEL_TRANSFER_OWNERSHIP 10⟩) (ok := true)
      (by decide) (by decide)
      (Sem.caoOwn (op := .transfer 10) (o := 6) (p := 10) rfl rfl (by decide) (by decide)) <|
    Sem.actsCall (s := 10) (c := ⟨1, 0, SEL_ACCEPT_OWNERSHIP⟩) (ok := true) (by decide)
      (by decide)
      (Sem.caoOwn (op := .accept) (o := 10) (p := 0) rfl rfl (by decide) (by decide)) <|
    Sem.actsNil, ?_⟩
  decide

theorem ZeroSetterWitness : Properties.ZeroSetterWitness := by
  refine ⟨wCfg_wellFormed, rfl, _, _,
    Sem.actsCall (by decide) (by decide) (w_multicallA rfl rfl rfl) Sem.actsNil, ?_, ?_, ?_⟩
  · intro inv pre x hm
    simp at hm
  · decide
  · rfl

theorem RenounceWitness : Properties.RenounceWitness := by
  refine ⟨wCfg_wellFormed, by decide, rfl, rfl,
    ⟨_, Sem.actsCall (by decide) (by decide) (w_setSetter rfl) <|
      Sem.actsCall (s := 6) (c := ⟨1, 0, SEL_RENOUNCE_OWNERSHIP⟩) (ok := true) (by decide)
        (by decide)
        (Sem.caoOwn (op := .renounce) (o := 0) (p := 0) rfl rfl (by decide) (by decide)) <|
      Sem.actsNil, ?_⟩,
    _, _,
    Sem.actsCall (by decide) (by decide) (w_multiplierOnChain rfl rfl) <|
    Sem.actsCall (s := 7) (c := ⟨1, 0, viaData 11 3 2⟩) (ok := true) (by decide) (by decide)
      (Sem.caoSetMultiplier (t := 11) (n := 3) (d := 2) rfl rfl (by decide) (by decide) rfl
        (Sem.external (by decide) (by decide) (by decide) Sem.actsNil)) <|
    Sem.actsNil, ?_⟩
  · decide
  · decide

/-- The owner's `multicall(wCallsB, true)` from `wS1`: its first call reaches the owner's code,
which renounces; its second call nominates `12` on diamond `4`. -/
theorem w_multicallOutlivesRenounce :
    Sem wCfg .acts wS1
      [.caoWrite 6 ⟨6, 0, 7⟩ (.own .renounce),
        .caoCall (.multicall 6 ⟨6, 0, 7⟩ wCallsB 0) ⟨6, 0, []⟩ true,
        .chainEntry 4 1 SEL_SET_PENDING_ADMIN,
        .caoCall (.multicall 6 ⟨6, 0, 7⟩ wCallsB 1) ⟨4, 0, withWord SEL_SET_PENDING_ADMIN 12⟩
          true]
      (wRenounced.setChain 4 ⟨1, 12⟩) :=
  Sem.actsCall (s := 6) (c := ⟨1, 0, SEL_MULTICALL ++ [2]⟩) (ok := true) (by decide)
    (by decide)
    (Sem.caoMulticall (cs := wCallsB) (rs := true) rfl (by decide) (by decide) rfl (by decide)
      (Sem.loopStep (c := ⟨6, 0, []⟩) (ok := true) (by decide)
        (Sem.external (by decide) (by decide) (by decide)
          (Sem.actsCall (s := 6) (c := ⟨1, 0, SEL_RENOUNCE_OWNERSHIP⟩) (ok := true)
            (by decide) (by decide)
            (Sem.caoOwn (op := .renounce) (o := 0) (p := 0) rfl rfl (by decide) (by decide))
            Sem.actsNil))
        (fun _ => rfl)
        (Sem.loopStep (c := ⟨4, 0, withWord SEL_SET_PENDING_ADMIN 12⟩) (ok := true)
          (by decide)
          (Sem.chainAdmin (op := .setPending 12) (p := ⟨1, 12⟩) (by decide) rfl (by decide)
            (by decide))
          (fun _ => rfl)
          (Sem.loopDone (by decide))))) Sem.actsNil

theorem MulticallOutlivesRenounce : Properties.MulticallOutlivesRenounce :=
  ⟨_, _, w_multicallOutlivesRenounce, rfl, rfl, by decide⟩

end Contracts.ChainAdminOwnable
