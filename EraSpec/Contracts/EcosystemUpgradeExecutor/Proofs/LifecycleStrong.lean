import EraSpec.Contracts.EcosystemUpgradeExecutor.Properties.LifecycleStrong
import EraSpec.Contracts.EcosystemUpgradeExecutor.Proofs.Lifecycle

/-!
# Proofs: the stage guards exactly, and abandonment as a live escape hatch

The exact guards and abandonment's effect are read off the `Step` constructors. Liveness
without `forward` is `ReservationTracksSlot` (the CTM domain is reserved for the pending
operation) followed by the `abandon` constructor. A prepared operation stays refused because
its stage 0 set the timer's `deadline` to `now + d`, which is positive, deadlines never
decrease (`run_deadline_mono`), and `Stage0RefusesForeignOrStartedTimer` refuses a started
timer. The recovery with `forward` is a case split on whether the slot and the reservation
are occupied, using `SlotEmptyIffStageNone`.
-/

namespace Contracts.EcosystemUpgradeExecutor

/-! ## The guards, exactly -/

theorem LifecycleStageGuardsExact : Properties.LifecycleStageGuardsExact := by
  intro K s op
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨s', h⟩
    cases h with
    | @stage0 _ t hp hop ht ha hs => exact ⟨hp, ha, hop, t, ht, hs⟩
  · rintro ⟨hp, ha, hop, t, ht, hs⟩
    exact ⟨_, Step.stage0 hp hop ht ha hs⟩
  · rintro ⟨s', h⟩
    cases h with
    | @stage1 _ t hp hst ht hd hact => exact ⟨hp, hst, hact, t, ht, hd⟩
  · rintro ⟨hp, hst, hact, t, ht, hd⟩
    exact ⟨_, Step.stage1 hp hst ht hd hact⟩
  · rintro ⟨s', h⟩
    cases h with
    | @stage2 _ t hp hst ht hd hact => exact ⟨hp, hst, hact, t, ht, hd⟩
  · rintro ⟨hp, hst, hact, t, ht, hd⟩
    exact ⟨_, Step.stage2 hp hst ht hd hact⟩
  · rintro ⟨s', h⟩
    cases h with
    | abandon hp ha => exact ⟨hp, ha⟩
  · rintro ⟨hp, ha⟩
    exact ⟨_, Step.abandon hp ha⟩

theorem LifecycleAbandonExact : Properties.LifecycleAbandonExact := by
  intro K s s'
  constructor
  · intro h
    cases h with
    | abandon hp ha => exact ⟨hp, ha, rfl⟩
  · rintro ⟨hp, ha, rfl⟩
    exact Step.abandon hp ha

/-! ## Abandonment is live -/

theorem LifecycleAbandonEnabledWhilePending : Properties.LifecycleAbandonEnabledWhilePending := by
  intro K s0 s ls h0 hr hnf hne
  have ha : s.active = s.pending := ReservationTracksSlot K s0 s ls h0 hr hnf
  exact ⟨_, Step.abandon hne (by rw [ha]; exact hne), ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩

theorem LifecycleFreeingIsStage2OrAbandon : Properties.LifecycleFreeingIsStage2OrAbandon := by
  intro K s s' l hne h0 h
  cases h with
  | @stage0 op t _ hop _ _ _ => exact absurd h0 hop
  | stage1 _ _ _ _ _ => exact absurd h0 hne
  | @stage2 op t hp hst _ _ _ => exact Or.inr ⟨by rw [hp], hst⟩
  | abandon _ _ => exact Or.inl rfl
  | tick _ => exact absurd h0 hne
  | startByGovernance _ _ => exact absurd h0 hne
  | changeDeadline _ _ _ => exact absurd h0 hne
  | forwardBegin _ => exact absurd h0 hne
  | forwardApply _ => exact absurd h0 hne
  | forwardRelease _ => exact absurd h0 hne

/-- A run from a positive timestamp that contains `stage0(op)`, where `op` names the
`GovernanceUpgradeTimer` `t`, ends with `t` started. -/
private lemma lifecycleStrong_run_stage0_started {K : Config} {s0 s : Sys} {ls : List Label}
    {op t : Address} {d a : ℕ} {g : Address} (hr : Run K s0 ls s) (hpos : 0 < s0.now)
    (ht : K.opTimer op = some t) (hk : K.timer t = .governance d a g)
    (hmem : Label.stage0 op ∈ ls) : s.deadline t ≠ 0 := by
  induction hr with
  | nil => simp at hmem
  | @cons sa sb sc l ls hs hr' ih =>
    rcases List.mem_cons.mp hmem with hl | hl
    · subst hl
      have hb : sb.deadline t ≠ 0 := by
        cases hs with
        | @stage0 _ t' _ _ ht' _ _ =>
          have htt : t' = t := Option.some.inj (ht'.symm.trans ht)
          subst htt
          show (startEffect K sa t').deadline t' ≠ 0
          rw [startEffect_deadline_gov hk, upd_eq]; omega
      intro h
      exact hb (Nat.eq_zero_of_le_zero (h ▸ run_deadline_mono hr' t))
    · exact ih (lt_of_lt_of_le hpos (step_now_mono hs)) hl

theorem LifecyclePreparedGovernanceOpStaysRefused :
    Properties.LifecyclePreparedGovernanceOpStaysRefused := by
  intro K s0 s s' ls ls' op t d a g hpos ht hk hr hmem hr'
  have h1 : s.deadline t ≠ 0 := lifecycleStrong_run_stage0_started hr hpos ht hk hmem
  have h2 : s'.deadline t ≠ 0 := fun h =>
    h1 (Nat.eq_zero_of_le_zero (h ▸ run_deadline_mono hr' t))
  exact Stage0RefusesForeignOrStartedTimer K s' op t d a g ht hk (Or.inr h2)

theorem LifecycleOwnerCanAlwaysReturnToIdle : Properties.LifecycleOwnerCanAlwaysReturnToIdle := by
  intro K s0 s ls h0 hr
  have hslot : s.pending = 0 ↔ s.stage = .none := SlotEmptyIffStageNone K s0 s ls h0 hr
  by_cases hp : s.pending = 0
  · by_cases ha : s.active = 0
    · exact ⟨[], s, Run.nil, by simp, by simp, ⟨hp, hslot.mp hp, ha⟩, rfl, rfl⟩
    · refine ⟨[.forwardRelease], _, Run.cons (Step.forwardRelease ha) Run.nil, by simp, ?_,
        ⟨hp, hslot.mp hp, rfl⟩, rfl, rfl⟩
      intro l hl
      rw [List.mem_singleton] at hl
      subst hl
      exact Or.inr trivial
  · by_cases ha : s.active = 0
    · refine ⟨[.forwardBegin s.pending, .abandon], _,
        Run.cons (Step.forwardBegin ha) (Run.cons (Step.abandon hp hp) Run.nil), by simp, ?_,
        ⟨rfl, rfl, rfl⟩, rfl, rfl⟩
      intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact Or.inr trivial
      · exact Or.inl rfl
    · refine ⟨[.abandon], _, Run.cons (Step.abandon hp ha) Run.nil, by simp, ?_,
        ⟨rfl, rfl, rfl⟩, rfl, rfl⟩
      intro l hl
      rw [List.mem_singleton] at hl
      exact Or.inl hl

/-! ## Witnesses and the countermodel -/

private lemma lifecycleStrong_wTimer7 : wK.timer 7 = .governance 0 1209600 10 := by decide
private lemma lifecycleStrong_wTimer8 : wK.timer 8 = .governance 10 1209600 10 := by decide

/-- After `stage0(2)` at `100`, timer `8`'s deadline is `110`. -/
private lemma lifecycleStrong_w2_deadline : (startEffect wK w0 8).deadline 8 = 110 := by
  rw [startEffect_deadline_gov lifecycleStrong_wTimer8, upd_eq]; rfl

/-- `stage0(2)` from the witness state: the coordinator may start timer `8`. -/
private lemma lifecycleStrong_startOk8 : StartOk wK w0 8 := by
  simp only [StartOk, lifecycleStrong_wTimer8]; exact ⟨rfl, rfl⟩

/-- `stage0(1)` from the witness state: the coordinator may start timer `7`. -/
private lemma lifecycleStrong_startOk7 : StartOk wK w0 7 := by
  simp only [StartOk, lifecycleStrong_wTimer7]; exact ⟨rfl, rfl⟩

/-- Timer `7`'s deadline has passed right after `stage0(1)` at `100` (zero delay). -/
private lemma lifecycleStrong_passed7 {s : Sys} (hd : s.deadline = (startEffect wK w0 7).deadline)
    (hn : s.now = 100) : DeadlinePassed wK s 7 := by
  simp only [DeadlinePassed, lifecycleStrong_wTimer7]
  rw [hd, hn, startEffect_deadline_gov lifecycleStrong_wTimer7, upd_eq]; decide

/-- Below timer `8`'s deadline `110`, `stage1(2)` is refused. -/
private lemma lifecycleStrong_no_stage1_2 {s : Sys} (hd : s.deadline 8 = 110) (hn : s.now < 110) :
    ¬ ∃ s', Step wK s (.stage1 2) s' := by
  rintro ⟨s', h⟩
  obtain ⟨_, _, _, t, ht, hp⟩ := (LifecycleStageGuardsExact _ _ _).2.1.mp ⟨s', h⟩
  have htt : t = 8 := (Option.some.inj ht).symm
  subst htt
  simp only [DeadlinePassed, lifecycleStrong_wTimer8] at hp
  omega

theorem LifecycleAbandonDuringDelayWitness : Properties.LifecycleAbandonDuringDelayWitness := by
  refine ⟨_, _, Run.cons (Step.stage0 (t := 8) rfl (by decide) (by decide) rfl
      lifecycleStrong_startOk8) Run.nil,
    lifecycleStrong_no_stage1_2 lifecycleStrong_w2_deadline ?b, Step.abandon ?c ?d, ⟨rfl, rfl, rfl⟩,
    lifecycleStrong_w2_deadline, ?f, _, Step.stage0 (t := 7) rfl (by decide) (by decide) rfl ?g⟩
  case b => show (startEffect wK w0 8).now < 110; rw [startEffect_now]; decide
  case c => show (2 : UInt256) ≠ 0; decide
  case d => show (2 : UInt256) ≠ 0; decide
  case f =>
    refine Stage0RefusesForeignOrStartedTimer wK _ 2 8 10 1209600 10 (by decide)
      lifecycleStrong_wTimer8 (Or.inr ?_)
    show (startEffect wK w0 8).deadline 8 ≠ 0
    rw [lifecycleStrong_w2_deadline]; decide
  case g =>
    simp only [StartOk, lifecycleStrong_wTimer7]
    refine ⟨rfl, ?_⟩
    show (startEffect wK w0 8).deadline 7 = 0
    rw [startEffect_deadline_gov lifecycleStrong_wTimer8, upd_ne _ _ (by decide)]
    rfl

theorem LifecycleAbandonAfterExecuteWitness : Properties.LifecycleAbandonAfterExecuteWitness := by
  refine ⟨_, _, Run.cons (Step.stage0 (t := 7) rfl (by decide) (by decide) rfl
      lifecycleStrong_startOk7)
    (Run.cons (Step.stage1 (t := 7) rfl rfl (by decide)
      (lifecycleStrong_passed7 rfl (startEffect_now _ _ _)) (by decide)) Run.nil), rfl,
    Step.abandon ?c ?d, ⟨rfl, rfl, rfl⟩, ?e⟩
  case c => show (1 : UInt256) ≠ 0; decide
  case d => show (1 : UInt256) ≠ 0; decide
  case e =>
    show upd (startEffect wK w0 7).legAppliedAt 1 (some (startEffect wK w0 7).now) 1 = some 100
    rw [upd_eq, startEffect_now]; rfl

theorem LifecycleForwardReleaseWedgesCoordinator :
    Properties.LifecycleForwardReleaseWedgesCoordinator := by
  refine ⟨_, Run.cons (Step.stage0 (t := 8) rfl (by decide) (by decide) rfl
      lifecycleStrong_startOk8)
    (Run.cons (Step.forwardRelease ?a) (Run.cons (Step.tick ?b) Run.nil)), rfl, rfl, ?dp,
    ?ab, ?st, _, _, Step.forwardBegin rfl, Step.abandon ?p ?q, ⟨rfl, rfl, rfl⟩⟩
  case a => show (2 : UInt256) ≠ 0; decide
  case b => show (startEffect wK w0 8).now < 110; rw [startEffect_now]; decide
  case dp =>
    simp only [DeadlinePassed, lifecycleStrong_wTimer8]
    show (startEffect wK w0 8).deadline 8 ≠ 0 ∧ (startEffect wK w0 8).deadline 8 ≤ 110
    rw [lifecycleStrong_w2_deadline]; decide
  case ab =>
    rintro ⟨s', h⟩
    exact ((LifecycleStageGuardsExact _ _ 0).2.2.2.mp ⟨s', h⟩).2 rfl
  case st =>
    intro op
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨s', h⟩
      exact (by decide : (2 : UInt256) ≠ 0) ((LifecycleStageGuardsExact _ _ op).1.mp ⟨s', h⟩).1
    · rintro ⟨s', h⟩
      exact ((LifecycleStageGuardsExact _ _ op).2.1.mp ⟨s', h⟩).2.2.1 rfl
    · rintro ⟨s', h⟩
      exact absurd ((LifecycleStageGuardsExact _ _ op).2.2.1.mp ⟨s', h⟩).2.1 (by decide)
  case p => show (2 : UInt256) ≠ 0; decide
  case q => show (2 : UInt256) ≠ 0; decide

theorem LifecycleTimestampZeroReprepares : Properties.LifecycleTimestampZeroReprepares := by
  refine ⟨_, ⟨rfl, rfl, rfl⟩, Run.cons (Step.stage0 (t := 7) rfl (by decide) (by decide) rfl ?a)
    (Run.cons (Step.abandon ?b ?c)
      (Run.cons (Step.stage0 (t := 7) rfl (by decide) (by decide) rfl ?d) Run.nil)),
    by decide, lifecycleStrong_wTimer7, by decide⟩
  case a => simp only [StartOk, lifecycleStrong_wTimer7]; exact ⟨rfl, rfl⟩
  case b => show (1 : UInt256) ≠ 0; decide
  case c => show (1 : UInt256) ≠ 0; decide
  case d =>
    simp only [StartOk, lifecycleStrong_wTimer7]
    refine ⟨rfl, ?_⟩
    show (startEffect wK { w0 with now := 0 } 7).deadline 7 = 0
    rw [startEffect_deadline_gov lifecycleStrong_wTimer7, upd_eq]

theorem LifecycleAbandonEnabledWhilePendingSatisfiable :
    Properties.LifecycleAbandonEnabledWhilePendingSatisfiable := by
  refine ⟨⟨rfl, rfl, rfl⟩,
    ⟨_, Run.cons (Step.stage0 (t := 8) rfl (by decide) (by decide) rfl
      lifecycleStrong_startOk8) Run.nil, ?nf1, ?p, rfl⟩,
    ⟨_, Run.cons (Step.stage0 (t := 7) rfl (by decide) (by decide) rfl
      lifecycleStrong_startOk7)
      (Run.cons (Step.stage1 (t := 7) rfl rfl (by decide)
        (lifecycleStrong_passed7 rfl (startEffect_now _ _ _)) (by decide)) Run.nil),
      ?nf2, ?q, rfl⟩⟩
  case nf1 =>
    intro l hl
    rcases List.mem_singleton.mp hl with rfl
    exact fun h => h
  case nf2 =>
    intro l hl
    rcases List.mem_cons.mp hl with rfl | hl
    · exact fun h => h
    · rcases List.mem_singleton.mp hl with rfl
      exact fun h => h
  case p => show (2 : UInt256) ≠ 0; decide
  case q => show (1 : UInt256) ≠ 0; decide

theorem LifecycleFreeingIsStage2OrAbandonSatisfiable :
    Properties.LifecycleFreeingIsStage2OrAbandonSatisfiable := by
  refine ⟨⟨_, _, Run.cons (Step.stage0 (t := 8) rfl (by decide) (by decide) rfl
      lifecycleStrong_startOk8) Run.nil, ?p, ?z, Step.abandon ?c ?d⟩,
    ⟨_, _, Run.cons (Step.stage0 (t := 7) rfl (by decide) (by decide) rfl
      lifecycleStrong_startOk7)
      (Run.cons (Step.stage1 (t := 7) rfl rfl (by decide)
        (lifecycleStrong_passed7 rfl (startEffect_now _ _ _)) (by decide)) Run.nil), ?q, ?z',
      Step.stage2 (t := 7) rfl rfl (by decide)
        (lifecycleStrong_passed7 rfl (startEffect_now _ _ _)) (by decide)⟩⟩
  case p => show (2 : UInt256) ≠ 0; decide
  case z => rfl
  case c => show (2 : UInt256) ≠ 0; decide
  case d => show (2 : UInt256) ≠ 0; decide
  case q => show (1 : UInt256) ≠ 0; decide
  case z' => rfl

theorem LifecyclePreparedGovernanceOpStaysRefusedSatisfiable :
    Properties.LifecyclePreparedGovernanceOpStaysRefusedSatisfiable := by
  refine ⟨by decide, by decide, lifecycleStrong_wTimer8, _, _,
    Run.cons (Step.stage0 (t := 8) rfl (by decide) (by decide) rfl lifecycleStrong_startOk8)
      (Run.cons (Step.abandon ?c ?d) Run.nil), by simp, Run.cons (Step.tick ?b) Run.nil⟩
  case c => show (2 : UInt256) ≠ 0; decide
  case d => show (2 : UInt256) ≠ 0; decide
  case b => show (startEffect wK w0 8).now < 200; rw [startEffect_now]; decide

theorem LifecycleOwnerCanAlwaysReturnToIdleSatisfiable :
    Properties.LifecycleOwnerCanAlwaysReturnToIdleSatisfiable := by
  refine ⟨⟨rfl, rfl, rfl⟩, _, Run.cons (Step.stage0 (t := 8) rfl (by decide) (by decide) rfl
      lifecycleStrong_startOk8) (Run.cons (Step.forwardRelease ?a) Run.nil), ?b, ?c⟩
  case a => show (2 : UInt256) ≠ 0; decide
  case b =>
    rintro ⟨hp, -, -⟩
    exact (by decide : (2 : UInt256) ≠ 0) hp
  case c =>
    intro l s' h hidle
    obtain ⟨hp', -, -⟩ := hidle
    cases h with
    | stage0 hp _ _ _ _ => exact (by decide : (2 : UInt256) ≠ 0) hp
    | stage2 _ _ _ _ hact => exact hact rfl
    | abandon _ ha => exact ha rfl
    | _ => exact (by decide : (2 : UInt256) ≠ 0) hp'

end Contracts.EcosystemUpgradeExecutor
