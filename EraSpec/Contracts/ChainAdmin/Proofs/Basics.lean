import EraSpec.Contracts.ChainAdmin.Specs.Model

/-!
# Proofs: shared lemmas for the `ChainAdmin` model

* map updates and state setters;
* `EnumerableSet.remove` keeps every other element and adds none;
* what the entry points of the restrictions can write;
* `sem_closed` / `reach_closed`: the invariant rule. A state predicate that every primitive
  write preserves holds along every run and in every state a multicall validated a call in. A
  write made by a `ChainAdmin` may use that every active restriction accepted the call in the
  state it executes from, and each write may use an assumption `Q` about the events of the run.
  The run-level results are instances.
-/

namespace Contracts.ChainAdmin

/-! ## Updates -/

@[simp] lemma upd_same {κ α : Type} [DecidableEq κ] (f : κ → α) (k : κ) (v : α) :
    upd f k v k = v := by simp [upd]

lemma upd_ne {κ α : Type} [DecidableEq κ] (f : κ → α) {k x : κ} (v : α) (h : x ≠ k) :
    upd f k v x = f x := by simp [upd, h]

lemma upd_apply {κ α : Type} [DecidableEq κ] (f : κ → α) (k x : κ) (v : α) :
    upd f k v x = if x = k then v else f x := rfl

/-! ## Restriction lists under the setters -/

lemma restrictions_addRestriction (S : State) (a x b : Address) :
    (S.addRestriction a x).restrictions b =
      if b = a then S.restrictions a ++ [x] else S.restrictions b := by
  unfold State.addRestriction State.setCA State.restrictions
  by_cases h : b = a
  · subst h; simp
  · simp [upd_ne _ _ h, h]

lemma restrictions_removeRestriction (S : State) (a x b : Address) :
    (S.removeRestriction a x).restrictions b =
      if b = a then enumRemove (S.restrictions a) x else S.restrictions b := by
  unfold State.removeRestriction State.setCA State.restrictions
  by_cases h : b = a
  · subst h; simp
  · simp [upd_ne _ _ h, h]

@[simp] lemma restrictions_setLocked (S : State) (a : Address) (v : Bool) (b : Address) :
    (S.setLocked a v).restrictions b = S.restrictions b := by
  unfold State.setLocked State.setCA State.restrictions
  by_cases h : b = a
  · subst h; simp
  · simp [upd_ne _ _ h]

@[simp] lemma restrictions_setAcr (S : State) (r : Address) (A : AcrState) (b : Address) :
    (S.setAcr r A).restrictions b = S.restrictions b := rfl

@[simp] lemma restrictions_setPerm (S : State) (p : Address) (P : PermState) (b : Address) :
    (S.setPerm p P).restrictions b = S.restrictions b := rfl

@[simp] lemma restrictions_setChain (S : State) (c : Address) (C : ChainState) (b : Address) :
    (S.setChain c C).restrictions b = S.restrictions b := rfl

@[simp] lemma restrictions_setExt (S : State) (e : Ext) (b : Address) :
    (S.setExt e).restrictions b = S.restrictions b := rfl

@[simp] lemma restrictions_tick (S : State) (b : Address) :
    S.tick.restrictions b = S.restrictions b := rfl

/-! ## `enumRemove` -/

/-- Every value of the removed set was in the set. -/
lemma mem_of_mem_enumRemove {l : List Address} {x y : Address} (hy : y ∈ enumRemove l x) :
    y ∈ l := by
  unfold enumRemove at hy
  have h1 := List.mem_of_mem_dropLast hy
  rcases List.mem_or_eq_of_mem_set h1 with h | h
  · exact h
  · subst h
    cases hl : l.getLast? with
    | none =>
        have : l = [] := List.getLast?_eq_none_iff.mp hl
        subst this; simp at h1
    | some z => simpa [hl] using List.mem_of_getLast? hl

/-- Removing `x` keeps every other value. -/
lemma mem_enumRemove {l : List Address} {x y : Address} (hx : x ∈ l) (hy : y ∈ l)
    (hne : y ≠ x) : y ∈ enumRemove l x := by
  unfold enumRemove
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
  have hi : l.idxOf x < l.length := List.idxOf_lt_length_of_mem hx
  have hix : l[l.idxOf x] = x := List.getElem_idxOf hi
  have hlast : l.getLast?.getD 0 = l[l.length - 1] := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]; rfl
  rw [List.mem_iff_getElem]
  by_cases hjl : j = l.length - 1
  · -- `y` is the last value; it moves into the removed slot
    have hil : l.idxOf x ≠ l.length - 1 := by
      intro h; apply hne; rw [← hix]; simp [hjl, h]
    refine ⟨l.idxOf x, ?_, ?_⟩
    · simp; omega
    · rw [List.getElem_dropLast, List.getElem_set_self, hlast]; simp [hjl]
  · have hji : j ≠ l.idxOf x := by
      intro h; apply hne; rw [← hix]; simp [h]
    refine ⟨j, ?_, ?_⟩
    · simp; omega
    · rw [List.getElem_dropLast, List.getElem_set_ne (Ne.symm hji)]

/-! ## What `PermanentRestriction`'s entry points write -/

/-- `permRun` emits only allowances by its own address. -/
lemma permRun_log {cfg : Config} {fac p s : Address} {P P' : PermState} {m : PermMsg}
    {L : List Entry} (h : permRun cfg fac p s P m = some (P', L)) :
    ∀ e ∈ L, ∃ hh, e = Entry.allowImpl p hh := by
  intro e he
  cases m <;> simp only [permRun] at h <;> split_ifs at h <;> cases h
  all_goals first
    | exact absurd he List.not_mem_nil
    | (split_ifs at he
       · exact ⟨_, List.mem_singleton.mp he⟩
       · exact absurd he List.not_mem_nil)

/-- A hash `permRun` leaves allowed was allowed before, or its allowance is among the events. -/
lemma permRun_allowed {cfg : Config} {fac p s : Address} {P P' : PermState} {m : PermMsg}
    {L : List Entry} (h : permRun cfg fac p s P m = some (P', L)) (hh : UInt256)
    (ha : P'.allowedAdminImplementations hh = true) :
    P.allowedAdminImplementations hh = true ∨ Entry.allowImpl p hh ∈ L := by
  cases m <;> simp only [permRun] at h <;> split_ifs at h <;> cases h
  all_goals first
    | exact Or.inl ha
    | (rename_i h0 b _
       by_cases hx : hh = h0
       · subst hx
         simp only [upd_same] at ha
         right; simp [ha]
       · left; simpa [upd_ne _ _ hx] using ha)

/-- `permRun` never clears a whitelisted L2 admin. -/
lemma permRun_l2_mono {cfg : Config} {fac p s : Address} {P P' : PermState} {m : PermMsg}
    {L : List Entry} (h : permRun cfg fac p s P m = some (P', L)) (x : Address)
    (hx : P.allowedL2Admins x = true) : P'.allowedL2Admins x = true := by
  cases m <;> simp only [permRun] at h <;> split_ifs at h <;> cases h
  all_goals first
    | exact hx
    | (simp only [upd_apply]; split_ifs <;> simp [hx])

/-- An L2 admin `permRun` whitelists is `computeCreateAddress(fac, n)` for `1 ≤ n ≤ 2^48`. -/
lemma permRun_l2_new {cfg : Config} {fac p s : Address} {P P' : PermState} {m : PermMsg}
    {L : List Entry} (h : permRun cfg fac p s P m = some (P', L)) (x : Address)
    (hx : P'.allowedL2Admins x = true) :
    P.allowedL2Admins x = true ∨ FactoryAddress cfg fac x := by
  cases m <;> simp only [permRun] at h <;> split_ifs at h <;> cases h
  all_goals first
    | exact Or.inl hx
    | (rename_i n hn0 hmax _
       by_cases hxe : x = cfg.createAddress fac n
       · exact Or.inr ⟨n, hn0, by omega, hxe⟩
       · left; simpa [upd_ne _ _ hxe] using hx)

/-! ## The invariant rule -/

lemma chainAdmin_ne_zero {cfg : Config} {a : Address} (hk : cfg.kind a = .chainAdmin) :
    cfg.WF → a ≠ 0 := by
  intro hwf h; subst h; rw [Config.WF] at hwf; rw [hwf] at hk; cases hk

/-- The call `c` that `s` makes from `S` was validated: if `s` is a `ChainAdmin`, the call is an
iteration of its multicall, so every active restriction accepted it in `S` for the invoker, and
the event the iteration emits satisfies `Q`. -/
def Validated (cfg : Config) (Q : Entry → Prop) (S : State) (s : Address) (c : Call) (ok : Bool) :
    Prop :=
  cfg.kind s = .chainAdmin → ∃ i, AllAccept cfg S s c i ∧ Q (.exec s i c ok S)

/-- `I` is preserved by every primitive write a successful entry point can make. `Q` is an
assumption about the events of the run. -/
structure Closed (cfg : Config) (Q : Entry → Prop) (I : State → Prop) : Prop where
  add : ∀ (S : State) (c : Call) (x : Address), cfg.kind c.target = .chainAdmin →
    (∃ i, AllAccept cfg S c.target c i ∧ Q (.exec c.target i c true S)) →
    4 ≤ c.data.length → c.data.take 4 = SEL_ADD_RESTRICTION →
    cfg.abi.addr (c.data.drop 4) = some x → supportsMagic cfg S x = true → I S →
    I (S.addRestriction c.target x)
  remove : ∀ (S : State) (c : Call) (x : Address), cfg.kind c.target = .chainAdmin →
    (∃ i, AllAccept cfg S c.target c i ∧ Q (.exec c.target i c true S)) →
    4 ≤ c.data.length → c.data.take 4 = SEL_REMOVE_RESTRICTION →
    cfg.abi.addr (c.data.drop 4) = some x → x ∈ S.restrictions c.target → I S →
    I (S.removeRestriction c.target x)
  lock : ∀ (S : State) (a : Address) (b : Bool), I S → I (S.setLocked a b)
  acr : ∀ (S : State) (s r : Address) (m : AcrMsg) (A' : AcrState), (cfg.WF → s ≠ 0) →
    cfg.kind r = .acr → acrRun s S.now (S.acr r) m = some A' → I S → I (S.setAcr r A')
  perm : ∀ (S : State) (s p bh fac : Address) (m : PermMsg) (P' : PermState) (L : List Entry),
    cfg.kind p = .perm bh fac → permRun cfg fac p s (S.perm p) m = some (P', L) →
    (∀ e ∈ L, Q e) → I S → I (S.setPerm p P')
  chain : ∀ (S : State) (s : Address) (c : Call) (C' : ChainState), (cfg.WF → s ≠ 0) →
    Validated cfg Q S s c true → cfg.kind c.target = .zkChain →
    chainExec cfg s (S.chain c.target) c.data = some C' → I S → I (S.setChain c.target C')
  ext : ∀ (S : State) (e : Ext), I S → I (S.setExt e)
  tick : ∀ (S : State), I S → I S.tick

/-- An emitted call was made by a `ChainAdmin`, from a state satisfying `I` in which every
active restriction accepted it. -/
def EntryOk (cfg : Config) (I : State → Prop) : Entry → Prop
  | .exec a i c _ pre => cfg.kind a = .chainAdmin ∧ I pre ∧ AllAccept cfg pre a c i
  | .allowImpl _ _ => True

/-- What is known when a judgement starts. -/
def Pre (cfg : Config) (Q : Entry → Prop) : Judgement → State → Prop
  | .call s c ok, S => (cfg.WF → s ≠ 0) ∧ Validated cfg Q S s c ok
  | .loop a _ _ _, _ => cfg.kind a = .chainAdmin
  | .acts, _ => True

/-- **The invariant rule, for one derivation.** -/
theorem sem_closed {cfg : Config} {Q : Entry → Prop} {I : State → Prop} (hI : Closed cfg Q I)
    {j : Judgement} {S S' : State} {L : List Entry} (h : Sem cfg j S L S') :
    (∀ e ∈ L, Q e) → Pre cfg Q j S → I S → I S' ∧ ∀ e ∈ L, EntryOk cfg I e := by
  induction h with
  | callFails => intro _ _ h0; exact ⟨h0, by simp⟩
  | caReceive => intro _ _ h0; exact ⟨h0, by simp⟩
  | @caAdd s c S x hk _ hlen hsel hdec hself hm _ =>
      intro _ hpre h0
      subst hself
      exact ⟨hI.add S c x hk (hpre.2 hk) hlen hsel hdec hm h0, by simp⟩
  | @caRemove s c S x hk _ hlen hsel hdec hself hx =>
      intro _ hpre h0
      subst hself
      exact ⟨hI.remove S c x hk (hpre.2 hk) hlen hsel hdec hx h0, by simp⟩
  | @caMulticall s c S S' L cs rs hk _ _ _ _ _ _ ih =>
      intro hQ _ h0
      obtain ⟨h1, hE⟩ := ih hQ hk (hI.lock _ _ _ h0)
      exact ⟨hI.lock _ _ _ h1, hE⟩
  | caView => intro _ _ h0; exact ⟨h0, by simp⟩
  | @acrCall s c S m A' hk _ _ hrun =>
      intro _ hpre h0
      exact ⟨hI.acr S s c.target m A' hpre.1 hk hrun h0, by simp⟩
  | acrView => intro _ _ h0; exact ⟨h0, by simp⟩
  | @permCall s c S bh fac m P' L hk _ _ hrun =>
      intro hQ _ h0
      refine ⟨hI.perm S s c.target bh fac m P' L hk hrun hQ h0, ?_⟩
      intro e he
      obtain ⟨hh, rfl⟩ := permRun_log hrun e he
      trivial
  | permView => intro _ _ h0; exact ⟨h0, by simp⟩
  | @chainAdminCall s c S C' hk _ hx =>
      intro _ hpre h0
      exact ⟨hI.chain S s c C' hpre.1 hpre.2 hk hx h0, by simp⟩
  | chainOther _ _ _ ih => intro hQ _ h0; exact ih hQ trivial h0
  | external _ _ ih => intro hQ _ h0; exact ih hQ trivial h0
  | loopNil => intro _ _ h0; exact ⟨h0, by simp⟩
  | @loopCons a i rs ok c cs S S1 S2 L1 L2 hacc _ _ _ ih1 ih2 =>
      intro hQ hk h0
      have hQ1 : ∀ e ∈ L1, Q e := fun e he => hQ e (by simp [he])
      have hQ2 : ∀ e ∈ L2, Q e := fun e he => hQ e (by simp [he])
      have hQe : Q (.exec a i c ok S) := hQ _ (by simp)
      obtain ⟨h1, hE1⟩ := ih1 hQ1 ⟨chainAdmin_ne_zero hk, fun _ => ⟨i, hacc, hQe⟩⟩ h0
      obtain ⟨h2, hE2⟩ := ih2 hQ2 hk h1
      refine ⟨h2, ?_⟩
      intro e he
      simp only [List.mem_append, List.mem_cons] at he
      rcases he with he | rfl | he
      · exact hE1 e he
      · exact ⟨hk, h0, hacc⟩
      · exact hE2 e he
  | actsRefl => intro _ _ h0; exact ⟨h0, by simp⟩
  | @actsCall s c ok S S1 S2 L1 L2 hs hs0 _ _ ih1 ih2 =>
      intro hQ _ h0
      obtain ⟨h1, hE1⟩ :=
        ih1 (fun e he => hQ e (by simp [he])) ⟨fun _ => hs0, fun h => absurd h hs⟩ h0
      obtain ⟨h2, hE2⟩ := ih2 (fun e he => hQ e (by simp [he])) trivial h1
      exact ⟨h2, fun e he => (List.mem_append.mp he).elim (hE1 e) (hE2 e)⟩
  | @actsExt e S S2 L _ ih => intro hQ _ h0; exact ih hQ trivial (hI.ext _ e h0)

/-- The invariant rule for one step. -/
theorem step_closed {cfg : Config} {Q : Entry → Prop} {I : State → Prop} (hI : Closed cfg Q I)
    {S S' : State} {L : List Entry} (h : Step cfg S L S') (hQ : ∀ e ∈ L, Q e) (h0 : I S) :
    I S' ∧ ∀ e ∈ L, EntryOk cfg I e := by
  cases h with
  | tx hs hs0 hsem => exact sem_closed hI hsem hQ ⟨fun _ => hs0, fun h => absurd h hs⟩ h0
  | ext e => exact ⟨hI.ext _ e h0, by simp⟩
  | tick => exact ⟨hI.tick _ h0, by simp⟩

/-- **The invariant rule, for runs.** If every write preserves `I`, given `Q` of the events,
then along a run whose events satisfy `Q`, `I` holds at the end, and every call a multicall made
was made by a `ChainAdmin` from a state satisfying `I` in which all its restrictions accepted. -/
theorem reach_closed {cfg : Config} {Q : Entry → Prop} {I : State → Prop} (hI : Closed cfg Q I)
    {S S' : State} {L : List Entry} (h : Reach cfg S L S') (hQ : ∀ e ∈ L, Q e) (h0 : I S) :
    I S' ∧ ∀ e ∈ L, EntryOk cfg I e := by
  induction h with
  | refl => exact ⟨h0, by simp⟩
  | tail _ hs ih =>
      obtain ⟨h1, hE1⟩ := ih (fun e he => hQ e (by simp [he]))
      obtain ⟨h2, hE2⟩ := step_closed hI hs (fun e he => hQ e (by simp [he])) h1
      exact ⟨h2, fun e he => (List.mem_append.mp he).elim (hE1 e) (hE2 e)⟩

/-- An entry of a run, unpacked. -/
theorem reach_entry {cfg : Config} {Q : Entry → Prop} {I : State → Prop} (hI : Closed cfg Q I)
    {S S' : State} {L : List Entry} (h : Reach cfg S L S') (hQ : ∀ e ∈ L, Q e) (h0 : I S)
    {a i : Address} {c : Call} {ok : Bool} {pre : State} (he : Entry.exec a i c ok pre ∈ L) :
    cfg.kind a = .chainAdmin ∧ I pre ∧ AllAccept cfg pre a c i :=
  (reach_closed hI h hQ h0).2 _ he

/-! ## What an accepting `PermanentRestriction` implies -/

/-- An active `PermanentRestriction` accepted the call. -/
lemma permValidates_of_allAccept {cfg : Config} {S : State} {a p bh fac i : Address} {c : Call}
    (hk : cfg.kind p = .perm bh fac) (hp : p ∈ S.restrictions a) (h : AllAccept cfg S a c i) :
    permValidates cfg bh p (S.perm p) S a c = true := by
  have := h p hp
  simpa [validates, hk] using this

/-- An active `PermanentRestriction` `p` does not accept `a.removeRestriction(p)` from `a`. -/
lemma not_remove_self {cfg : Config} {S : State} {a p bh fac i x : Address} {c : Call}
    (hk : cfg.kind p = .perm bh fac) (hp : p ∈ S.restrictions a) (h : AllAccept cfg S a c i)
    (ht : c.target = a) (hlen : 4 ≤ c.data.length) (hsel : c.data.take 4 = SEL_REMOVE_RESTRICTION)
    (hdec : cfg.abi.addr (c.data.drop 4) = some x) : x ≠ p := by
  have hv := permValidates_of_allAccept hk hp h
  simp only [permValidates, Bool.and_eq_true] at hv
  have h3 := hv.2
  have hlen' : ¬ c.data.length < 4 := by omega
  simpa [validateRemoveRestriction, ht, hlen', hsel, hdec] using h3

end Contracts.ChainAdmin
