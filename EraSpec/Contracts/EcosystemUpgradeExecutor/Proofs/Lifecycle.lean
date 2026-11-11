import EraSpec.Contracts.EcosystemUpgradeExecutor.Properties.Lifecycle

/-!
# Proofs: the coordinator's lifecycle, and what its timer guarantees

The invariant `LInv` carries three facts along runs from an idle state: the slot is empty
exactly when the stage is `None`, the ghost `preparedAt` is not in the future, and a
pending operation's `GovernanceUpgradeTimer` has its deadline at least `INITIAL_DELAY`
after `preparedAt`. `run_hist` ties `preparedAt` to the `stage0` in the run that set the
pending operation. The headline is then `deadline ≤ now` from `checkDeadline`.
-/

namespace Contracts.EcosystemUpgradeExecutor

lemma upd_eq {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : upd f a b a = b := by
  simp [upd]

lemma upd_ne {α β : Type} [DecidableEq α] (f : α → β) {x a : α} (b : β) (h : x ≠ a) :
    upd f a b x = f x := by
  simp [upd, h]

/-! ## Field lemmas -/

lemma startEffect_now (K : Config) (s : Sys) (t : Address) : (startEffect K s t).now = s.now := by
  unfold startEffect; split <;> rfl

lemma startEffect_pending (K : Config) (s : Sys) (t : Address) :
    (startEffect K s t).pending = s.pending := by
  unfold startEffect; split <;> rfl

lemma startEffect_active (K : Config) (s : Sys) (t : Address) :
    (startEffect K s t).active = s.active := by
  unfold startEffect; split <;> rfl

lemma startEffect_deadline_gov {K : Config} {s : Sys} {t : Address} {d a : ℕ} {g : Address}
    (h : K.timer t = .governance d a g) :
    (startEffect K s t).deadline = upd s.deadline t (s.now + d) := by
  simp [startEffect, h]

lemma startEffect_deadline_other {K : Config} {s : Sys} {t : Address}
    (h : ∀ d a g, K.timer t ≠ .governance d a g) : (startEffect K s t).deadline = s.deadline := by
  unfold startEffect
  split
  · rename_i d a g hg; exact absurd hg (h d a g)
  · rfl

/-! ## Monotone quantities -/

lemma step_now_mono {K : Config} {s s' : Sys} {l : Label} (h : Step K s l s') : s.now ≤ s'.now := by
  cases h with
  | tick hlt => exact le_of_lt hlt
  | stage0 _ _ _ _ _ => exact le_of_eq (startEffect_now _ _ _).symm
  | _ => exact le_rfl

lemma startOk_deadline {K : Config} {s : Sys} {t : Address} {d a : ℕ} {g : Address}
    (h : K.timer t = .governance d a g) (hs : StartOk K s t) : g = K.C ∧ s.deadline t = 0 := by
  simp only [StartOk, h] at hs; exact hs

lemma step_deadline_mono {K : Config} {s s' : Sys} {l : Label} (h : Step K s l s') (x : Address) :
    s.deadline x ≤ s'.deadline x := by
  cases h with
  | @stage0 op t _ _ _ _ hs =>
    show s.deadline x ≤ (startEffect K s t).deadline x
    rcases hk : K.timer t with ⟨d, a, g⟩ | _ | _
    · rw [startEffect_deadline_gov hk]
      by_cases hx : x = t
      · subst hx; rw [upd_eq]; rw [(startOk_deadline hk hs).2]; exact Nat.zero_le _
      · rw [upd_ne _ _ hx]
    all_goals (rw [startEffect_deadline_other (by intro d a g; rw [hk]; simp)])
  | @startByGovernance t d a g _ h0 =>
    show s.deadline x ≤ upd s.deadline t (s.now + d) x
    by_cases hx : x = t
    · subst hx; rw [upd_eq, h0]; exact Nat.zero_le _
    · rw [upd_ne _ _ hx]
  | @changeDeadline t y d a g _ hlt _ =>
    show s.deadline x ≤ upd s.deadline t y x
    by_cases hx : x = t
    · subst hx; rw [upd_eq]; exact le_of_lt hlt
    · rw [upd_ne _ _ hx]
  | _ => exact le_rfl

lemma run_now_mono {K : Config} {s s' : Sys} {ls : List Label} (h : Run K s ls s') : s.now ≤ s'.now := by
  induction h with
  | nil => exact le_rfl
  | cons hs _ ih => exact le_trans (step_now_mono hs) ih

lemma run_deadline_mono {K : Config} {s s' : Sys} {ls : List Label} (h : Run K s ls s') (x : Address) :
    s.deadline x ≤ s'.deadline x := by
  induction h with
  | nil => exact le_rfl
  | cons hs _ ih => exact le_trans (step_deadline_mono hs x) ih

/-! ## How a step moves the slot -/

lemma step_slot {K : Config} {s s' : Sys} {l : Label} (h : Step K s l s') :
    (∃ op, l = .stage0 op ∧ s.pending = 0 ∧ op ≠ 0 ∧ s'.pending = op ∧ s'.stage = .prepared ∧
      s'.preparedAt = s.now) ∨
    (∃ op, l = .stage1 op ∧ s.pending = op ∧ s.stage = .prepared ∧ s'.pending = s.pending ∧
      s'.stage = .executed ∧ s'.preparedAt = s.preparedAt) ∨
    ((s.pending ≠ 0 ∨ s.stage = .executed) ∧ s'.pending = 0 ∧ s'.stage = .none ∧
      ∀ op, l ≠ .stage0 op) ∨
    (s'.pending = s.pending ∧ s'.stage = s.stage ∧ s'.preparedAt = s.preparedAt ∧
      ∀ op, l ≠ .stage0 op) := by
  cases h with
  | @stage0 op t hp hop _ _ _ => exact Or.inl ⟨op, rfl, hp, hop, rfl, rfl, rfl⟩
  | @stage1 op t hp hst _ _ _ => exact Or.inr (Or.inl ⟨op, rfl, hp, hst, rfl, rfl, rfl⟩)
  | @stage2 op t hp hst _ _ _ => exact Or.inr (Or.inr (Or.inl ⟨Or.inr hst, rfl, rfl, by simp⟩))
  | abandon hp _ => exact Or.inr (Or.inr (Or.inl ⟨Or.inl hp, rfl, rfl, by simp⟩))
  | tick _ => exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, by simp⟩))
  | startByGovernance _ _ => exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, by simp⟩))
  | changeDeadline _ _ _ => exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, by simp⟩))
  | forwardBegin _ => exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, by simp⟩))
  | forwardApply _ => exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, by simp⟩))
  | forwardRelease _ => exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, by simp⟩))

/-! ## The invariant -/

/-- The lifecycle invariant. -/
structure LInv (K : Config) (s : Sys) : Prop where
  slot : s.pending = 0 ↔ s.stage = .none
  past : s.preparedAt ≤ s.now
  delay : s.pending ≠ 0 → ∀ t d a g, K.opTimer s.pending = some t →
    K.timer t = .governance d a g → s.preparedAt + d ≤ s.deadline t

lemma idle_inv {K : Config} {s : Sys} (h : Idle s) (hp : s.preparedAt ≤ s.now) : LInv K s := by
  obtain ⟨h1, h2, _⟩ := h
  exact ⟨by simp [h1, h2], hp, fun hne => absurd h1 hne⟩

lemma step_inv {K : Config} {s s' : Sys} {l : Label} (hI : LInv K s) (h : Step K s l s') :
    LInv K s' := by
  obtain ⟨hslot, hpast, hdelay⟩ := hI
  cases h with
  | tick hlt =>
    exact ⟨hslot, le_trans hpast (le_of_lt hlt), hdelay⟩
  | @stage0 op t' hp hop ht' _ hs =>
    refine ⟨by simp [hop], le_of_eq (startEffect_now _ _ _).symm, ?_⟩
    intro _ t d a g ht hk
    show s.now + d ≤ (startEffect K s t').deadline t
    have htt : t' = t := Option.some.inj (ht'.symm.trans ht)
    subst htt
    rw [startEffect_deadline_gov hk, upd_eq]
  | @stage1 op t hp hst _ _ _ =>
    have hne : s.pending ≠ 0 := fun h => by rw [hslot.mp h] at hst; cases hst
    exact ⟨by simp [hne], hpast, fun _ => hdelay hne⟩
  | stage2 _ _ _ _ _ => exact ⟨by simp, hpast, fun h => absurd rfl h⟩
  | abandon _ _ => exact ⟨by simp, hpast, fun h => absurd rfl h⟩
  | @startByGovernance t' d' a' g' hk' h0 =>
    refine ⟨hslot, hpast, ?_⟩
    intro hne t d a g ht hk
    show s.preparedAt + d ≤ upd s.deadline t' (s.now + d') t
    by_cases htt : t = t'
    · subst htt
      rw [hk] at hk'
      cases hk'
      rw [upd_eq]; omega
    · rw [upd_ne _ _ htt]; exact hdelay hne t d a g ht hk
  | @changeDeadline t' y d' a' g' _ hlt _ =>
    refine ⟨hslot, hpast, ?_⟩
    intro hne t d a g ht hk
    show s.preparedAt + d ≤ upd s.deadline t' y t
    have := hdelay hne t d a g ht hk
    by_cases htt : t = t'
    · subst htt; rw [upd_eq]; omega
    · rw [upd_ne _ _ htt]; exact this
  | forwardBegin _ => exact ⟨hslot, hpast, hdelay⟩
  | forwardApply _ => exact ⟨hslot, hpast, hdelay⟩
  | forwardRelease _ => exact ⟨hslot, hpast, hdelay⟩

lemma run_inv {K : Config} {s s' : Sys} {ls : List Label} (hI : LInv K s) (h : Run K s ls s') :
    LInv K s' := by
  induction h with
  | nil => exact hI
  | cons hs _ ih => exact ih (step_inv hI hs)

/-- From an idle start, whatever its ghost `preparedAt`, the slot clause and the delay
clause hold along the run: while the slot is occupied, `preparedAt` was set by the `stage0`
that filled it. -/
lemma idle_run_inv {K : Config} {s0 s : Sys} {ls : List Label} (h0 : Idle s0) (h : Run K s0 ls s) :
    (s.pending = 0 ↔ s.stage = .none) ∧ (s.pending ≠ 0 → ∀ t d a g, K.opTimer s.pending = some t →
      K.timer t = .governance d a g → s.preparedAt + d ≤ s.deadline t) := by
  -- `LInv` with its `past` clause required only while the slot is occupied.
  have key : ∀ {s1 s2 : Sys} {ls : List Label}, Run K s1 ls s2 →
      (s1.pending = 0 ↔ s1.stage = .none) →
      (s1.pending ≠ 0 → s1.preparedAt ≤ s1.now ∧ ∀ t d a g, K.opTimer s1.pending = some t →
        K.timer t = .governance d a g → s1.preparedAt + d ≤ s1.deadline t) →
      (s2.pending = 0 ↔ s2.stage = .none) ∧
      (s2.pending ≠ 0 → s2.preparedAt ≤ s2.now ∧ ∀ t d a g, K.opTimer s2.pending = some t →
        K.timer t = .governance d a g → s2.preparedAt + d ≤ s2.deadline t) := by
    intro s1 s2 ls hr
    induction hr with
    | nil => exact fun a b => ⟨a, b⟩
    | @cons sa sb sc l ls hs _ ih =>
      intro hslot hocc
      apply ih
      · rcases step_slot hs with ⟨op, _, _, hop, h1, h2, _⟩ | ⟨op, _, _, hst, h1, h2, _⟩ |
          ⟨_, h1, h2, _⟩ | ⟨h1, h2, _, _⟩
        · simp [h1, h2, hop]
        · rw [h1, h2]
          have : sa.pending ≠ 0 := fun h => by rw [hslot.mp h] at hst; exact absurd hst (by simp)
          simp [this]
        · simp [h1, h2]
        · rw [h1, h2]; exact hslot
      · intro hne
        by_cases hpa : sa.pending = 0
        · -- the slot was empty, so `l` is the `stage0` that filled it
          rcases step_slot hs with ⟨op, rfl, _, _, _, _, _⟩ | ⟨op, _, _, _, h2, _, _⟩ |
            ⟨_, h1, _, _⟩ | ⟨h1, _, _, _⟩
          · cases hs with
            | @stage0 _ t' _ _ ht' _ hst =>
              refine ⟨le_of_eq (startEffect_now _ _ _).symm, ?_⟩
              intro t d a g ht hk
              show sa.now + d ≤ (startEffect K sa t').deadline t
              have htt : t' = t := Option.some.inj (ht'.symm.trans ht)
              subst htt
              rw [startEffect_deadline_gov hk, upd_eq]
          · exact absurd (h2.trans hpa) hne
          · exact absurd h1 hne
          · exact absurd (h1.trans hpa) hne
        · have hI : LInv K sa := ⟨hslot, (hocc hpa).1, fun h => (hocc h).2⟩
          have hI' := step_inv hI hs
          exact ⟨hI'.past, hI'.delay hne⟩
  obtain ⟨hp, hs, _⟩ := h0
  have := key h (by simp [hp, hs]) (fun h => absurd hp h)
  exact ⟨this.1, fun hne => (this.2 hne).2⟩

/-! ## Where `preparedAt` comes from -/

lemma run_hist {K : Config} {s0 s : Sys} {ls : List Label} (h : Run K s0 ls s) (hne : s.pending ≠ 0) :
    (∃ l1 l2 sa sb, ls = l1 ++ .stage0 s.pending :: l2 ∧ Run K s0 l1 sa ∧
      Step K sa (.stage0 s.pending) sb ∧ Run K sb l2 s ∧ (∀ l ∈ l2, ∀ op', l ≠ .stage0 op') ∧
      sa.now = s.preparedAt) ∨
    (s.pending = s0.pending ∧ s.preparedAt = s0.preparedAt ∧ ∀ l ∈ ls, ∀ op', l ≠ .stage0 op') := by
  induction h with
  | nil => exact Or.inr ⟨rfl, rfl, by simp⟩
  | @cons sa sb sc l ls hs hr ih =>
    rcases ih hne with ⟨l1, l2, sx, sy, hls, hr1, hst, hr2, hno, hnow⟩ | ⟨hp, hprep, hno⟩
    · exact Or.inl ⟨l :: l1, l2, sx, sy, by rw [hls]; rfl, Run.cons hs hr1, hst, hr2, hno, hnow⟩
    · rcases step_slot hs with ⟨op, rfl, _, _, h1, _, h3⟩ | ⟨op, rfl, _, _, h1, _, h3⟩ |
        ⟨_, h1, _, _⟩ | ⟨h1, _, h3, hns⟩
      · left
        have hop : sc.pending = op := hp.trans h1
        rw [hop]
        exact ⟨[], ls, sa, sb, rfl, Run.nil, hs, hr, hno, by rw [hprep, h3]⟩
      · right
        refine ⟨hp.trans h1, hprep.trans h3, ?_⟩
        intro l hl op'
        rcases List.mem_cons.mp hl with rfl | hl
        · simp
        · exact hno l hl op'
      · exact absurd (hp.trans h1) hne
      · right
        refine ⟨hp.trans h1, hprep.trans h3, ?_⟩
        intro l' hl op'
        rcases List.mem_cons.mp hl with rfl | hl
        · exact hns op'
        · exact hno l' hl op'

/-! ## The lifecycle -/

theorem StageGuards : Properties.StageGuards := by
  intro K s s' op
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · cases h with
    | @stage0 _ t hp hop ht ha hs => exact ⟨hp, ha, hop, t, ht, hs⟩
  · cases h with
    | @stage1 _ t hp hst ht hd _ => exact ⟨hp, hst, t, ht, hd⟩
  · cases h with
    | @stage2 _ t hp hst ht hd _ => exact ⟨hp, hst, t, ht, hd⟩
  · cases h with
    | abandon hp _ => exact hp

theorem StagesMoveForward : Properties.StagesMoveForward := by
  intro K s s' l hslot h
  rcases step_slot h with ⟨op, _, hp, hop, h1, h2, _⟩ | ⟨op, _, _, hst, h1, h2, _⟩ |
    ⟨hp, h1, h2, _⟩ | ⟨h1, h2, _, _⟩
  · exact Or.inr (Or.inl ⟨hp, hslot.mp hp, by rw [h1]; exact hop, h2⟩)
  · have : s.pending ≠ 0 := fun h => by rw [hslot.mp h] at hst; exact absurd hst (by simp)
    exact Or.inr (Or.inr (Or.inl ⟨this, hst, h1, h2⟩))
  · have : s.pending ≠ 0 := by
      rcases hp with hp | hp
      · exact hp
      · exact fun h => by rw [hslot.mp h] at hp; cases hp
    exact Or.inr (Or.inr (Or.inr ⟨this, h1, h2⟩))
  · exact Or.inl ⟨h1, h2⟩

theorem SlotEmptyIffStageNone : Properties.SlotEmptyIffStageNone :=
  fun _ _ _ _ h0 h => (idle_run_inv h0 h).1

theorem ReservationTracksSlot : Properties.ReservationTracksSlot := by
  intro K s0 s ls h0 h hl
  obtain ⟨hp, _, ha⟩ := h0
  have key : ∀ {s1 s2 : Sys} {ls : List Label}, Run K s1 ls s2 → (∀ l ∈ ls, ¬ l.isForward) →
      s1.active = s1.pending → s2.active = s2.pending := by
    intro s1 s2 ls hr
    induction hr with
    | nil => exact fun _ h => h
    | @cons sa sb sc l ls hs _ ih =>
      intro hl heq
      apply ih (fun l' hm => hl l' (List.mem_cons_of_mem _ hm))
      have hl0 := hl l (List.mem_cons_self)
      cases hs with
      | stage0 _ _ _ _ _ => rfl
      | forwardBegin _ => exact absurd trivial hl0
      | forwardApply _ => exact absurd trivial hl0
      | forwardRelease _ => exact absurd trivial hl0
      | stage2 _ _ _ _ _ => rfl
      | abandon _ _ => rfl
      | _ => exact heq
  exact key h hl (by rw [hp, ha])

theorem Stage0RefusesForeignOrStartedTimer : Properties.Stage0RefusesForeignOrStartedTimer := by
  rintro K s op t d a g ht hk hbad ⟨s', h⟩
  cases h with
  | @stage0 _ t' _ _ ht' _ hs =>
    have htt : t' = t := Option.some.inj (ht'.symm.trans ht)
    subst htt
    obtain ⟨hg, h0⟩ := startOk_deadline hk hs
    rcases hbad with hbad | hbad
    · exact hbad hg
    · exact hbad h0

lemma no_stage0_after_start {K : Config} {s s' : Sys} {ls : List Label} {op t : Address} {d a : ℕ}
    {g : Address} (h : Run K s ls s') (ht : K.opTimer op = some t) (hk : K.timer t = .governance d a g)
    (h0 : s.deadline t ≠ 0) : ls.count (.stage0 op) = 0 := by
  induction h with
  | nil => rfl
  | @cons sa sb _ l ls hs _ ih =>
    have hb : sb.deadline t ≠ 0 := fun h => h0 (Nat.eq_zero_of_le_zero (h ▸ step_deadline_mono hs t))
    rw [List.count_cons, ih hb]
    by_cases hl : l = .stage0 op
    · subst hl
      exact absurd (Stage0RefusesForeignOrStartedTimer K sa op t d a g ht hk (Or.inr h0) ⟨_, hs⟩) id
    · simp [hl]

theorem GovernanceTimerPreparesOnce : Properties.GovernanceTimerPreparesOnce := by
  intro K s0 s ls op t d a g hpos ht hk h
  induction h with
  | nil => simp
  | @cons sa sb sc l ls hs hr ih =>
    rw [List.count_cons]
    by_cases hl : l = .stage0 op
    · subst hl
      have hb : sb.deadline t ≠ 0 := by
        cases hs with
        | @stage0 _ t' _ _ ht' _ _ =>
          have htt : t' = t := Option.some.inj (ht'.symm.trans ht)
          subst htt
          show (startEffect K sa t').deadline t' ≠ 0
          rw [startEffect_deadline_gov hk, upd_eq]; omega
      rw [no_stage0_after_start hr ht hk hb]; simp
    · have := ih (lt_of_lt_of_le hpos (step_now_mono hs))
      simpa [hl] using this

/-! ## The timer -/

theorem ExecutionWaitsForTheNamedTimer : Properties.ExecutionWaitsForTheNamedTimer := by
  intro K s0 s s' ls op t d a g h0 hr hs ht hk
  obtain ⟨hp, hst, t', ht', hd⟩ := (StageGuards K s s' op).2.1 hs
  have htt : t' = t := Option.some.inj (ht'.symm.trans ht)
  subst htt
  obtain ⟨hslot, hdel⟩ := idle_run_inv h0 hr
  have hne : s.pending ≠ 0 := fun h => by rw [hslot.mp h] at hst; exact absurd hst (by simp)
  have hbound := hdel hne t' d a g (by rw [hp]; exact ht) hk
  simp only [DeadlinePassed, hk] at hd
  rcases run_hist hr hne with ⟨l1, l2, sa, sb, hls, hr1, hst0, hr2, hno, hnow⟩ | ⟨hp0, _, _⟩
  · rw [hp] at hls hst0
    exact ⟨l1, l2, sa, sb, hls, hr1, hst0, hr2, hno, by omega⟩
  · exact absurd (hp0.trans h0.1) hne

/-! ## Countermodels and the witness -/

private lemma wTimer7 : wK.timer 7 = .governance 0 1209600 10 := by decide
private lemma wTimer8 : wK.timer 8 = .governance 10 1209600 10 := by decide
private lemma wTimer9 : wK.timer 9 = .permissive := by decide

theorem ZeroDelayTimerPasses : Properties.ZeroDelayTimerPasses := by
  refine ⟨_, Run.cons (Step.stage0 (t := 7) rfl (by decide) (by decide) rfl ?a)
    (Run.cons (Step.stage1 (t := 7) rfl rfl (by decide) ?b (by decide))
      (Run.cons (Step.stage2 (t := 7) rfl rfl (by decide) ?c (by decide)) Run.nil)),
    wTimer7, ?d, ?e, rfl, rfl, rfl⟩
  case a => simp only [StartOk, wTimer7]; exact ⟨rfl, rfl⟩
  case b =>
    simp only [DeadlinePassed, wTimer7]
    show (startEffect wK w0 7).deadline 7 ≠ 0 ∧ (startEffect wK w0 7).deadline 7 ≤ (startEffect wK w0 7).now
    rw [startEffect_deadline_gov wTimer7, startEffect_now, upd_eq]; decide
  case c =>
    simp only [DeadlinePassed, wTimer7]
    show (startEffect wK w0 7).deadline 7 ≠ 0 ∧ (startEffect wK w0 7).deadline 7 ≤ (startEffect wK w0 7).now
    rw [startEffect_deadline_gov wTimer7, startEffect_now, upd_eq]; decide
  case d => show (startEffect wK w0 7).now = 100; rw [startEffect_now]; rfl
  case e =>
    show upd (startEffect wK w0 7).legAppliedAt 1 (some (startEffect wK w0 7).now) 1 = some 100
    rw [upd_eq, startEffect_now]; rfl

theorem PermissiveTimerPasses : Properties.PermissiveTimerPasses := by
  refine ⟨_, Run.cons (Step.stage0 (t := 9) rfl (by decide) (by decide) rfl ?a)
    (Run.cons (Step.stage1 (t := 9) rfl rfl (by decide) ?b (by decide))
      (Run.cons (Step.stage2 (t := 9) rfl rfl (by decide) ?c (by decide)) Run.nil)),
    wTimer9, ?d, ?e, rfl, rfl, rfl⟩
  case a => simp only [StartOk, wTimer9]
  case b => simp only [DeadlinePassed, wTimer9]
  case c => simp only [DeadlinePassed, wTimer9]
  case d => show (startEffect wK w0 9).now = 100; rw [startEffect_now]; rfl
  case e =>
    show upd (startEffect wK w0 9).legAppliedAt 3 (some (startEffect wK w0 9).now) 3 = some 100
    rw [upd_eq, startEffect_now]; rfl

/-- After `stage0(2)` at `100`, timer `8`'s deadline is `110`. -/
private lemma w2_deadline : (startEffect wK w0 8).deadline 8 = 110 := by
  rw [startEffect_deadline_gov wTimer8, upd_eq]; rfl

/-- At a state whose timer `8` deadline is `110` and whose clock is below it, `stage1(2)` is
refused. -/
private lemma no_stage1_before {s : Sys} (hd : s.deadline 8 = 110) (hn : s.now < 110) :
    ¬ ∃ s', Step wK s (.stage1 2) s' := by
  rintro ⟨s', h⟩
  obtain ⟨_, _, t, ht, hp⟩ := (StageGuards _ _ _ _).2.1 h
  have htt : t = 8 := (Option.some.inj ht).symm
  subst htt
  simp only [DeadlinePassed, wTimer8] at hp
  omega

theorem ForwardAppliesLegBeforeTheDelay : Properties.ForwardAppliesLegBeforeTheDelay := by
  refine ⟨_, Run.cons (Step.stage0 (t := 8) rfl (by decide) (by decide) rfl ?a)
    (Run.cons (Step.forwardApply (by decide)) Run.nil), wTimer8, ?d, ?e, ?f⟩
  case a => simp only [StartOk, wTimer8]; exact ⟨rfl, rfl⟩
  case d => show (startEffect wK w0 8).now = 100; rw [startEffect_now]; rfl
  case e =>
    show upd (startEffect wK w0 8).legAppliedAt 2 (some (startEffect wK w0 8).now) 2 = some 100
    rw [upd_eq, startEffect_now]; rfl
  case f =>
    refine no_stage1_before ?_ ?_
    · show (startEffect wK w0 8).deadline 8 = 110; exact w2_deadline
    · show (startEffect wK w0 8).now < 110; rw [startEffect_now]; decide

theorem TimerBoundIsTight : Properties.TimerBoundIsTight := by
  refine ⟨_, Run.cons (Step.stage0 (t := 8) rfl (by decide) (by decide) rfl ?a)
    (Run.cons (Step.tick ?b) Run.nil), wTimer8, no_stage1_before ?g (by decide),
    _, _, Step.tick (by decide : (109 : ℕ) < 110), Step.stage1 (t := 8) rfl rfl (by decide) ?c
      (by decide), rfl⟩
  case a => simp only [StartOk, wTimer8]; exact ⟨rfl, rfl⟩
  case b => show (startEffect wK w0 8).now < 109; rw [startEffect_now]; decide
  case g => show (startEffect wK w0 8).deadline 8 = 110; exact w2_deadline
  case c =>
    simp only [DeadlinePassed, wTimer8]
    show (startEffect wK w0 8).deadline 8 ≠ 0 ∧ (startEffect wK w0 8).deadline 8 ≤ 110
    rw [w2_deadline]; decide

end Contracts.EcosystemUpgradeExecutor
