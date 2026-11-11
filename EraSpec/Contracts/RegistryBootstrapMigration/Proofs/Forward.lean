import EraSpec.Contracts.RegistryBootstrapMigration.Properties.Forward
import EraSpec.Contracts.RegistryBootstrapMigration.Proofs.Authority

/-!
# Proofs: forwarded calls and the authority model's label set

A covered call is one `AStep` or none, so a forward is an `ARun` by induction over its calls
(`opStep_arun`, `frun_arun`).

The folder README argued that the existing run results cover forwards. Two lemmas check that
composition: `noReparking_of_coveredForwards` (`NoReparkingAfterMigrate` through
`RunsWithForwardsAreRuns`) and `parked_ctm_of_coveredForward`
(`ParkedCTMLeavesOnlyByNomineeAccept`, iterated, through `ForwardIsARun`).

The stated run results across forwards are stronger. Each is an induction over calls with a
per-call frame, and the step case for the model's own transactions is `NoReparkingAfterMigrate`
on a one-step run.

The renounce countermodel rests on an invariant of `ARun`: both owners stay nonzero
(`arun_owners_ne_zero`). The swap countermodels and the witnesses are concrete runs.
-/

namespace Contracts.RegistryBootstrapMigration

/-! ## Runs of the model's labels -/

lemma arun_append {K : Config} {s s₁ s₂ : AState} {ls₁ ls₂ : List Label}
    (h₁ : ARun K s ls₁ s₁) (h₂ : ARun K s₁ ls₂ s₂) : ARun K s (ls₁ ++ ls₂) s₂ := by
  induction h₁ with
  | nil => exact h₂
  | cons hs _ ih => exact ARun.cons hs (ih h₂)

/-! ## A covered call is a run of its labels -/

lemma opStep_arun {K : Config} {a : Address} {s s' : AState} {op : Op}
    (haM : a ≠ K.M) (ha0 : a ≠ 0) (hin : op.InLabelSet) (h : OpStep K a s op s') :
    ARun K s op.labels s' := by
  cases h with
  | ctmTransferOwnership ho =>
      exact ARun.cons (AStep.nominate (by rw [ho]; exact haM)) ARun.nil
  | ctmAcceptOwnership hp =>
      subst hp
      exact ARun.cons (AStep.accept ha0 haM) ARun.nil
  | ctmRenounceOwnership _ | paRenounceOwnership _ | ctmCodeSwap _ => exact False.elim hin
  | ctmSetVersion ho => exact ARun.cons (AStep.legacyMove (by rw [ho]; exact haM)) ARun.nil
  | paTransferOwnership ho hx =>
      exact ARun.cons (AStep.transferPA (by rw [ho]; exact haM) hx) ARun.nil
  | migrate hm => exact ARun.cons (AStep.migrate hm) ARun.nil
  | untracked => exact ARun.nil

lemma frun_arun {K : Config} {s s' : AState} {cs : List Call} (h : FRun K s cs s')
    (hc : ∀ c ∈ cs, c.Covered K) : ARun K s (cs.flatMap Call.labels) s' := by
  induction h with
  | nil => exact ARun.nil
  | @cons s₁ s₂ s₃ c cs hstep _ ih =>
      obtain ⟨h1, h2, h3⟩ := hc c List.mem_cons_self
      rw [List.flatMap_cons]
      exact arun_append (opStep_arun h1 h2 h3 hstep)
        (ih fun c' hc' => hc c' (List.mem_cons_of_mem _ hc'))

/-- What a call's labels are: none, or exactly one, which is an other-actor label or
`migrate` and hands authority to the migration only if the call does. -/
lemma op_labels_cases (op : Op) :
    op.labels = [] ∨ ∃ l, op.labels = [l] ∧ (l.OtherActor ∨ l = .migrate) ∧
      ∀ K : Config, l.handsToMigration K → op.handsToMigration K := by
  cases op with
  | ctmRenounceOwnership | paRenounceOwnership | ctmCodeSwap | untracked => exact Or.inl rfl
  | migrate => exact Or.inr ⟨_, rfl, Or.inr rfl, fun _ => id⟩
  | _ => exact Or.inr ⟨_, rfl, Or.inl trivial, fun _ => id⟩

lemma op_labels_otherActor {op : Op} {l : Label} (h : l ∈ op.labels) :
    l.OtherActor ∨ l = .migrate := by
  rcases op_labels_cases op with h0 | ⟨l', h1, h2, _⟩
  · simp [h0] at h
  · rw [h1, List.mem_singleton] at h; subst h; exact h2

lemma op_labels_hands {K : Config} {op : Op} {l : Label} (h : l ∈ op.labels)
    (hh : l.handsToMigration K) : op.handsToMigration K := by
  rcases op_labels_cases op with h0 | ⟨l', h1, _, h3⟩
  · simp [h0] at h
  · rw [h1, List.mem_singleton] at h; subst h; exact h3 K hh

/-- Several transactions in a row are one `FRun` of their concatenated calls. -/
lemma frun_append {K : Config} {s s₁ s₂ : AState} {cs₁ cs₂ : List Call}
    (h₁ : FRun K s cs₁ s₁) (h₂ : FRun K s₁ cs₂ s₂) : FRun K s (cs₁ ++ cs₂) s₂ := by
  induction h₁ with
  | nil => exact h₂
  | cons hs _ ih => exact FRun.cons hs (ih h₂)

lemma xrun_arun {K : Config} {s s' : AState} {xs : List XLabel} (h : XRun K s xs s')
    (hc : ∀ x ∈ xs, x.Covered K) : ARun K s (xs.flatMap XLabel.labels) s' := by
  induction h with
  | nil => exact ARun.nil
  | @cons s₁ s₂ s₃ x xs hstep _ ih =>
      rw [List.flatMap_cons]
      refine arun_append ?_ (ih fun x' hx' => hc x' (List.mem_cons_of_mem _ hx'))
      have hx := hc x List.mem_cons_self
      cases hstep with
      | tx ha => exact ARun.cons ha ARun.nil
      | forward hf => exact frun_arun hf hx

/-! ## Per-call frames -/

/-- One `AStep` from a spent state with nothing parked keeps both, unless it hands authority
to the migration: `NoReparkingAfterMigrate` on a one-step run. -/
lemma astep_keeps_unparked {K : Config} {s s' : AState} {l : Label}
    (hx : s.executed = true) (hp : ¬ ParkedOnMigration K s) (hh : ¬ l.handsToMigration K)
    (h : AStep K s l s') : s'.executed = true ∧ ¬ ParkedOnMigration K s' :=
  ⟨(step_spent hx h).1,
    NoReparkingAfterMigrate K s s' [l] hx hp (ARun.cons h ARun.nil)
      (fun l' hl' => by rw [List.mem_singleton.mp hl']; exact hh)⟩

/-- One call from a spent state with nothing parked keeps both, unless it hands authority to
the migration or replaces the CTM's code. Whoever sends it. -/
lemma opStep_keeps_unparked {K : Config} {a : Address} {s s' : AState} {op : Op}
    (hx : s.executed = true) (hp : ¬ ParkedOnMigration K s) (hh : ¬ op.handsToMigration K)
    (hsw : ¬ op.swapsCtmCode) (h : OpStep K a s op s') :
    s'.executed = true ∧ ¬ ParkedOnMigration K s' := by
  simp only [ParkedOnMigration, not_or] at hp ⊢
  obtain ⟨ho, hpe, hpa⟩ := hp
  have h0 : ¬ (0 : Address) = K.M := fun h0 => K.migNonzero h0.symm
  cases h with
  | ctmTransferOwnership _ => exact ⟨hx, ho, hh, hpa⟩
  | ctmAcceptOwnership hq => exact ⟨hx, hq ▸ hpe, h0, hpa⟩
  | ctmRenounceOwnership _ => exact ⟨hx, h0, h0, hpa⟩
  | ctmSetVersion _ => exact ⟨hx, ho, hpe, hpa⟩
  | paTransferOwnership _ _ => exact ⟨hx, ho, hpe, hh⟩
  | paRenounceOwnership _ => exact ⟨hx, ho, hpe, h0⟩
  | ctmCodeSwap _ => exact absurd trivial hsw
  | migrate hm => exact Bool.noConfusion ((migrate_guards hm).1.symm.trans hx)
  | untracked => exact ⟨hx, ho, hpe, hpa⟩

lemma frun_keeps_unparked {K : Config} {s s' : AState} {cs : List Call} (h : FRun K s cs s') :
    s.executed = true → ¬ ParkedOnMigration K s → (∀ c ∈ cs, ¬ c.op.handsToMigration K) →
    (∀ c ∈ cs, ¬ c.op.swapsCtmCode) → s'.executed = true ∧ ¬ ParkedOnMigration K s' := by
  induction h with
  | nil => intro hx hp _ _; exact ⟨hx, hp⟩
  | cons hstep _ ih =>
      intro hx hp hh hsw
      obtain ⟨hx', hp'⟩ := opStep_keeps_unparked hx hp (hh _ List.mem_cons_self)
        (hsw _ List.mem_cons_self) hstep
      exact ih hx' hp' (fun c hc => hh c (List.mem_cons_of_mem _ hc))
        (fun c hc => hsw c (List.mem_cons_of_mem _ hc))

/-- One call while the spent migration owns the CTM, sent by someone else and not replacing
the CTM's code: the owner and the nomination stay, or the call is the nominee's accept. -/
lemma opStep_parked_ctm {K : Config} {a : Address} {s s' : AState} {op : Op}
    (ho : s.ctmOwner = K.M) (hx : s.executed = true) (haM : a ≠ K.M)
    (hsw : ¬ op.swapsCtmCode) (h : OpStep K a s op s') :
    (s'.ctmOwner = K.M ∧ s'.ctmPending = s.ctmPending ∧ s'.executed = true) ∨
      (op = .ctmAcceptOwnership ∧ a = s.ctmPending) := by
  cases h with
  | ctmTransferOwnership ho' | ctmRenounceOwnership ho' | ctmSetVersion ho' =>
      exact absurd (ho'.symm.trans ho) haM
  | ctmAcceptOwnership hq => exact Or.inr ⟨rfl, hq.symm⟩
  | paTransferOwnership _ _ | paRenounceOwnership _ | untracked => exact Or.inl ⟨ho, rfl, hx⟩
  | ctmCodeSwap _ => exact absurd trivial hsw
  | migrate hm => exact Bool.noConfusion ((migrate_guards hm).1.symm.trans hx)

lemma frun_parked_ctm {K : Config} {s s' : AState} {cs : List Call} (h : FRun K s cs s') :
    s.ctmOwner = K.M → s.executed = true → (∀ c ∈ cs, c.sender ≠ K.M) →
    (∀ c ∈ cs, ¬ c.op.swapsCtmCode) →
    (s'.ctmOwner = K.M ∧ s'.ctmPending = s.ctmPending) ∨
      Call.mk s.ctmPending .ctmAcceptOwnership ∈ cs := by
  induction h with
  | nil => intro ho _ _ _; exact Or.inl ⟨ho, rfl⟩
  | @cons s₁ s₂ s₃ c cs hstep _ ih =>
      intro ho hx hs hsw
      rcases opStep_parked_ctm ho hx (hs c List.mem_cons_self) (hsw c List.mem_cons_self)
          hstep with ⟨ho₂, hp₂, hx₂⟩ | ⟨hop, ha⟩
      · rcases ih ho₂ hx₂ (fun c' hc' => hs c' (List.mem_cons_of_mem _ hc'))
            (fun c' hc' => hsw c' (List.mem_cons_of_mem _ hc')) with ⟨h1, h2⟩ | hmem
        · exact Or.inl ⟨h1, h2.trans hp₂⟩
        · rw [hp₂] at hmem
          exact Or.inr (List.mem_cons_of_mem _ hmem)
      · right
        obtain ⟨sender, op⟩ := c
        simp only at hop ha
        subst hop ha
        exact List.mem_cons_self

/-- One call while the migration owns the `ProxyAdmin`, sent by someone else: the `ProxyAdmin`
stays, or the call is `migrate()`. -/
lemma opStep_parked_pa {K : Config} {a : Address} {s s' : AState} {op : Op}
    (hpa : s.paOwner = K.M) (haM : a ≠ K.M) (h : OpStep K a s op s') :
    s'.paOwner = K.M ∨ op = .migrate := by
  cases h with
  | paTransferOwnership hpa' _ | paRenounceOwnership hpa' | ctmCodeSwap hpa' =>
      exact absurd (hpa'.symm.trans hpa) haM
  | migrate _ => exact Or.inr rfl
  | _ => exact Or.inl hpa

lemma frun_parked_pa {K : Config} {s s' : AState} {cs : List Call} (h : FRun K s cs s') :
    s.paOwner = K.M → (∀ c ∈ cs, c.sender ≠ K.M) →
    s'.paOwner = K.M ∨ ∃ c ∈ cs, c.op = .migrate := by
  induction h with
  | nil => intro hpa _; exact Or.inl hpa
  | @cons s₁ s₂ s₃ c cs hstep _ ih =>
      intro hpa hs
      rcases opStep_parked_pa hpa (hs c List.mem_cons_self) hstep with hpa₂ | hm
      · rcases ih hpa₂ (fun c' hc' => hs c' (List.mem_cons_of_mem _ hc')) with h' | ⟨c', hc', hm'⟩
        · exact Or.inl h'
        · exact Or.inr ⟨c', List.mem_cons_of_mem _ hc', hm'⟩
      · exact Or.inr ⟨c, List.mem_cons_self, hm⟩

/-- One call by a nonzero sender. An ownerless `ProxyAdmin` stays ownerless. A CTM with
neither owner nor nominee keeps neither, unless the call replaces its code, which needs a
`ProxyAdmin` owner. -/
lemma opStep_stranded {K : Config} {a : Address} {s s' : AState} {op : Op}
    (ha0 : a ≠ 0) (h : OpStep K a s op s') :
    (s.paOwner = 0 → s'.paOwner = 0) ∧
      (s.ctmOwner = 0 → s.ctmPending = 0 →
        (s'.ctmOwner = 0 ∧ s'.ctmPending = 0) ∨ (s.paOwner ≠ 0 ∧ op.swapsCtmCode)) := by
  cases h with
  | ctmTransferOwnership ho | ctmRenounceOwnership ho | ctmSetVersion ho =>
      exact ⟨id, fun h0 _ => absurd (ho.symm.trans h0) ha0⟩
  | ctmAcceptOwnership hq => exact ⟨id, fun _ h0 => absurd (hq.symm.trans h0) ha0⟩
  | paTransferOwnership hpa' _ | paRenounceOwnership hpa' =>
      exact ⟨fun hpa => absurd (hpa'.symm.trans hpa) ha0, fun h0 h1 => Or.inl ⟨h0, h1⟩⟩
  | ctmCodeSwap hpa' =>
      exact ⟨fun hpa => absurd (hpa'.symm.trans hpa) ha0,
        fun _ _ => Or.inr ⟨by rw [hpa']; exact ha0, trivial⟩⟩
  | migrate hm =>
      obtain ⟨_, hc, hpa, _⟩ := migrate_guards hm
      refine ⟨fun h0 => absurd (hpa.symm.trans h0) K.migNonzero, fun h0 h1 => ?_⟩
      have hne : ¬ s.ctmPending = K.M := by rw [h1]; exact fun h => K.migNonzero h.symm
      unfold claim at hc
      rw [ite_eq_right hne] at hc
      exact absurd (hc.symm.trans h0) K.migNonzero
  | untracked => exact ⟨id, fun h0 h1 => Or.inl ⟨h0, h1⟩⟩

/-! ## Both owners stay nonzero along the model's runs -/

lemma migrate_owners {K : Config} {s s' : AState} (h : MigrateStep K s s') :
    s'.paOwner = K.m.E ∧ K.m.E ≠ 0 ∧ (s'.ctmOwner = K.M ∨ s'.ctmOwner = K.m.E) := by
  cases h with
  | mk _ h2 _ _ _ _ _ h8 =>
      unfold executorAccept
      refine ⟨?_, h8, ?_⟩ <;> split <;> (try split) <;>
        first | rfl | exact Or.inr rfl | exact Or.inl h2

lemma astep_owners_ne_zero {K : Config} {s s' : AState} {l : Label} (h : AStep K s l s')
    (h1 : s.ctmOwner ≠ 0) (h2 : s.paOwner ≠ 0) : s'.ctmOwner ≠ 0 ∧ s'.paOwner ≠ 0 := by
  have hmig : ∀ {t t' : AState}, MigrateStep K t t' → t'.ctmOwner ≠ 0 ∧ t'.paOwner ≠ 0 := by
    intro t t' hm
    obtain ⟨hpa, hE, ho⟩ := migrate_owners hm
    exact ⟨ho.elim (fun h => h ▸ K.migNonzero) (fun h => h ▸ hE), hpa ▸ hE⟩
  cases h with
  | nominate _ => exact ⟨h1, h2⟩
  | accept hp _ => exact ⟨hp, h2⟩
  | transferPA _ hx => exact ⟨h1, hx⟩
  | legacyMove _ => exact ⟨h1, h2⟩
  | migrate hm => exact hmig hm
  | bundle _ _ hm _ => exact hmig hm

lemma arun_owners_ne_zero {K : Config} {s s' : AState} {ls : List Label} (h : ARun K s ls s') :
    s.ctmOwner ≠ 0 → s.paOwner ≠ 0 → s'.ctmOwner ≠ 0 ∧ s'.paOwner ≠ 0 := by
  induction h with
  | nil => intro h1 h2; exact ⟨h1, h2⟩
  | cons hs _ ih =>
      intro h1 h2
      obtain ⟨h1', h2'⟩ := astep_owners_ne_zero hs h1 h2
      exact ih h1' h2'

end Contracts.RegistryBootstrapMigration

/-! ## Certificates -/

namespace Contracts.RegistryBootstrapMigration

theorem ForwardIsARun : Properties.ForwardIsARun := by
  intro K s s' cs hc h
  refine ⟨frun_arun h hc, ?_, ?_⟩
  · intro l hl
    obtain ⟨c, _, hl⟩ := List.mem_flatMap.mp hl
    exact op_labels_otherActor hl
  · intro l hl hh
    obtain ⟨c, hc', hl⟩ := List.mem_flatMap.mp hl
    exact ⟨c, hc', op_labels_hands hl hh⟩

theorem RunsWithForwardsAreRuns : Properties.RunsWithForwardsAreRuns := by
  intro K s s' xs hc h
  refine ⟨xrun_arun h hc, ?_⟩
  intro l hl hh
  obtain ⟨x, hx, hl⟩ := List.mem_flatMap.mp hl
  refine ⟨x, hx, ?_⟩
  cases x with
  | tx l' =>
      simp only [XLabel.labels, List.mem_singleton] at hl
      subst hl
      exact hh
  | forward cs =>
      obtain ⟨c, hc', hl⟩ := List.mem_flatMap.mp hl
      exact ⟨c, hc', op_labels_hands hl hh⟩

/-- The composition the folder README argued for: `NoReparkingAfterMigrate`, applied through
`RunsWithForwardsAreRuns`, covers runs whose forwards are covered. `NoReparkingAcrossForwards`
below states more: it also covers renounces and makes no premise on senders. -/
lemma noReparking_of_coveredForwards {K : Config} {s s' : AState} {xs : List XLabel}
    (hx : s.executed = true) (hp : ¬ ParkedOnMigration K s) (h : XRun K s xs s')
    (hc : ∀ x ∈ xs, x.Covered K) (hh : ∀ x ∈ xs, ¬ x.handsToMigration K) :
    ¬ ParkedOnMigration K s' := by
  obtain ⟨hrun, hlab⟩ := RunsWithForwardsAreRuns K s s' xs hc h
  refine NoReparkingAfterMigrate K s s' _ hx hp hrun fun l hl hl' => ?_
  obtain ⟨x, hx', hx''⟩ := hlab l hl hl'
  exact hh x hx' hx''

/-- `ParkedCTMLeavesOnlyByNomineeAccept`, iterated along a run of the model's labels: while
the spent migration owns the CTM, the owner and the nomination stay unless the run contains
an accept. -/
lemma parked_ctm_run {K : Config} {s s' : AState} {ls : List Label} (h : ARun K s ls s') :
    s.ctmOwner = K.M → s.executed = true →
    (s'.ctmOwner = K.M ∧ s'.ctmPending = s.ctmPending) ∨ Label.accept ∈ ls := by
  induction h with
  | nil => intro ho _; exact Or.inl ⟨ho, rfl⟩
  | @cons s₁ s₂ s₃ l ls hs _ ih =>
      intro ho hx
      rcases ParkedCTMLeavesOnlyByNomineeAccept K s₁ s₂ l ho hx hs with ⟨ho₂, hp₂⟩ | ⟨hl, _, _⟩
      · rcases ih ho₂ (step_spent hx hs).1 with ⟨h1, h2⟩ | hmem
        · exact Or.inl ⟨h1, h2.trans hp₂⟩
        · exact Or.inr (List.mem_cons_of_mem _ hmem)
      · subst hl
        exact Or.inr List.mem_cons_self

/-- Only an `acceptOwnership()` call has the label `accept`. -/
lemma accept_mem_labels {op : Op} (h : Label.accept ∈ op.labels) :
    op = .ctmAcceptOwnership := by
  cases op <;> simp_all [Op.labels]

/-- The composition for the CTM frame: through `ForwardIsARun`, `ParkedCTMLeavesOnlyByNomineeAccept`
says a covered forward leaves a parked CTM parked unless one of its calls is an
`acceptOwnership()`. `ForwardMovesParkedCTMOnlyByNomineeAccept` below states more: the accept
is the nominee's, and the calls need not be covered. -/
lemma parked_ctm_of_coveredForward {K : Config} {s s' : AState} {cs : List Call}
    (ho : s.ctmOwner = K.M) (hx : s.executed = true) (hc : ∀ c ∈ cs, c.Covered K)
    (h : FRun K s cs s') :
    (s'.ctmOwner = K.M ∧ s'.ctmPending = s.ctmPending) ∨
      ∃ c ∈ cs, c.op = .ctmAcceptOwnership := by
  rcases parked_ctm_run (ForwardIsARun K s s' cs hc h).1 ho hx with hkeep | hmem
  · exact Or.inl hkeep
  · obtain ⟨c, hc', hl⟩ := List.mem_flatMap.mp hmem
    exact Or.inr ⟨c, hc', accept_mem_labels hl⟩

theorem NoReparkingAcrossForwards : Properties.NoReparkingAcrossForwards := by
  intro K s s' xs hx hp h hh hsw
  induction h with
  | nil => exact hp
  | @cons s₁ s₂ s₃ x xs hstep _ ih =>
      have hh0 := hh x List.mem_cons_self
      have hsw0 := hsw x List.mem_cons_self
      have key : s₂.executed = true ∧ ¬ ParkedOnMigration K s₂ := by
        cases hstep with
        | tx ha => exact astep_keeps_unparked hx hp hh0 ha
        | forward hf =>
            exact frun_keeps_unparked hf hx hp (fun c hc h' => hh0 ⟨c, hc, h'⟩)
              (fun c hc h' => hsw0 ⟨c, hc, h'⟩)
      exact ih key.1 key.2 (fun x' hx' => hh x' (List.mem_cons_of_mem _ hx'))
        (fun x' hx' => hsw x' (List.mem_cons_of_mem _ hx'))

theorem ForwardMovesParkedCTMOnlyByNomineeAccept :
    Properties.ForwardMovesParkedCTMOnlyByNomineeAccept :=
  fun _ _ _ _ ho hx hs hsw h => frun_parked_ctm h ho hx hs hsw

theorem ForwardMovesParkedProxyAdminOnlyByMigrate :
    Properties.ForwardMovesParkedProxyAdminOnlyByMigrate :=
  fun _ _ _ _ hpa hs h => frun_parked_pa h hpa hs

theorem LabelsAreCoveredCalls : Properties.LabelsAreCoveredCalls := by
  intro K s s' l ho hpa hb h
  cases h with
  | @nominate x hne =>
      exact ⟨⟨s.ctmOwner, .ctmTransferOwnership x⟩, ⟨hne, ho, trivial⟩, rfl,
        FRun.cons (OpStep.ctmTransferOwnership rfl) FRun.nil⟩
  | accept hp hpM =>
      exact ⟨⟨s.ctmPending, .ctmAcceptOwnership⟩, ⟨hpM, hp, trivial⟩, rfl,
        FRun.cons (OpStep.ctmAcceptOwnership rfl) FRun.nil⟩
  | @transferPA x hne hx =>
      exact ⟨⟨s.paOwner, .paTransferOwnership x⟩, ⟨hne, hpa, trivial⟩, rfl,
        FRun.cons (OpStep.paTransferOwnership rfl hx) FRun.nil⟩
  | @legacyMove v r hne =>
      exact ⟨⟨s.ctmOwner, .ctmSetVersion v r⟩, ⟨hne, ho, trivial⟩, rfl,
        FRun.cons (OpStep.ctmSetVersion rfl) FRun.nil⟩
  | migrate hm =>
      obtain ⟨_, _, _, hA, _⟩ := migrate_guards hm
      obtain ⟨e, he⟩ := executorAuthorities_E hA
      exact ⟨⟨K.m.E, .migrate⟩, ⟨exec_ne_mig he, (migrate_owners hm).2.1, trivial⟩, rfl,
        FRun.cons (OpStep.migrate hm) FRun.nil⟩
  | bundle _ _ _ _ => exact absurd rfl hb

theorem LabelRunsKeepOwnersNonzero : Properties.LabelRunsKeepOwnersNonzero :=
  fun _ _ _ _ h => arun_owners_ne_zero h

theorem RenouncedAuthorityIsStranded : Properties.RenouncedAuthorityIsStranded := by
  intro K s s' cs hs h
  induction h with
  | nil => exact ⟨id, fun h0 h1 => Or.inl ⟨h0, h1⟩⟩
  | @cons s₁ s₂ s₃ c cs hstep _ ih =>
      obtain ⟨hpa₁, hctm₁⟩ := opStep_stranded (hs c List.mem_cons_self) hstep
      obtain ⟨hpa₂, hctm₂⟩ := ih (fun c' hc' => hs c' (List.mem_cons_of_mem _ hc'))
      refine ⟨fun h0 => hpa₂ (hpa₁ h0), fun h0 h1 => ?_⟩
      rcases hctm₁ h0 h1 with ⟨h0', h1'⟩ | ⟨hne, hsw⟩
      · rcases hctm₂ h0' h1' with hfin | ⟨hne₂, c', hc', hsw'⟩
        · exact Or.inl hfin
        · by_cases hpa : s₁.paOwner = 0
          · exact absurd (hpa₁ hpa) hne₂
          · exact Or.inr ⟨hpa, c', List.mem_cons_of_mem _ hc', hsw'⟩
      · exact Or.inr ⟨hne, c, List.mem_cons_self, hsw⟩

end Contracts.RegistryBootstrapMigration

/-! ## Countermodels and witnesses -/

namespace Contracts.RegistryBootstrapMigration

private lemma fwAuth (g : Bool) : ExecutorAuthorities (wConfig g) :=
  ⟨⟨9, 0, 1, 2, g⟩, ⟨9, 0, 0, 0, true⟩, by simp [wConfig, wExec, wManifest],
    by simp [wConfig, wExec, wManifest], rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Governance's hand-over, then `migrate()`, in the witness configuration. -/
private lemma fwMigrate (g : Bool) :
    MigrateStep (wConfig g) wHanded
      (executorAccept (wConfig g) (handOn (wConfig g) (claim (wConfig g) wHanded))) :=
  MigrateStep.mk rfl (by cases g <;> decide) rfl (fwAuth g) rfl rfl (by cases g <;> decide)
    (by cases g <;> decide)

private lemma fwMigratePost : MigrateStep (wConfig true) wHanded wPost := by
  have hcomp : executorAccept (wConfig true) (handOn (wConfig true)
      (claim (wConfig true) wHanded)) = wPost := by decide
  exact hcomp ▸ fwMigrate true

private lemma fwBundle : AStep (wConfig true) wPre .bundle wPost :=
  AStep.bundle (by decide) (by decide) fwMigratePost
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, fwAuth true, rfl⟩

private lemma not_parked_post : ¬ ParkedOnMigration (wConfig true) wPost := by
  unfold ParkedOnMigration; decide

theorem ForwardedRenounceLeavesTheLabelSet : Properties.ForwardedRenounceLeavesTheLabelSet := by
  have hpa : FRun (wConfig true) wPost [⟨3, .paRenounceOwnership⟩] ⟨3, 0, 0, 35, 60, true⟩ :=
    FRun.cons (OpStep.paRenounceOwnership rfl) FRun.nil
  have hctm : FRun (wConfig true) wPost [⟨3, .ctmRenounceOwnership⟩] ⟨0, 0, 3, 35, 60, true⟩ :=
    FRun.cons (OpStep.ctmRenounceOwnership rfl) FRun.nil
  refine ⟨⟨_, hpa, rfl, by unfold ParkedOnMigration; decide, ?_⟩,
    ⟨_, hctm, rfl, by unfold ParkedOnMigration; decide, ?_⟩⟩
  · rintro ⟨ls, h⟩
    exact (arun_owners_ne_zero h (by decide) (by decide)).2 rfl
  · rintro ⟨ls, h⟩
    exact (arun_owners_ne_zero h (by decide) (by decide)).1 rfl

theorem ForwardCtmSwapReparks : Properties.ForwardCtmSwapReparks := by
  have hrun : XRun (wConfig true) wPost [.forward [⟨3, .ctmCodeSwap 50 0 35 60⟩]]
      ⟨50, 0, 3, 35, 60, true⟩ :=
    XRun.cons (XStep.forward (FRun.cons (OpStep.ctmCodeSwap rfl) FRun.nil)) XRun.nil
  refine ⟨rfl, not_parked_post, ?_, ⟨_, List.mem_singleton_self _, trivial⟩, _, hrun,
    Or.inl rfl⟩
  rintro ⟨c, hc, hh⟩
  obtain rfl := List.mem_singleton.mp hc
  exact hh

theorem ForwardCtmSwapMovesParkedCTM : Properties.ForwardCtmSwapMovesParkedCTM := by
  have hrun : FRun (wConfig false) wParked [⟨3, .ctmCodeSwap 9 0 35 60⟩] ⟨9, 0, 3, 35, 60, true⟩ :=
    FRun.cons (OpStep.ctmCodeSwap rfl) FRun.nil
  exact ⟨rfl, rfl, _, hrun, rfl, by decide⟩

theorem ForwardWitness : Properties.ForwardWitness := by
  have hsucc : FRun (wConfig true) wPost wSuccession ⟨7, 0, 7, 36, 61, true⟩ :=
    FRun.cons (OpStep.ctmSetVersion rfl)
      (FRun.cons (OpStep.ctmTransferOwnership rfl)
        (FRun.cons (OpStep.paTransferOwnership rfl (by decide))
          (FRun.cons OpStep.untracked
            (FRun.cons (OpStep.ctmAcceptOwnership rfl) FRun.nil))))
  refine ⟨?_, fwBundle, rfl, not_parked_post, by decide, by decide,
    ⟨_, AStep.nominate (by decide)⟩, _, XRun.cons (XStep.forward hsucc) XRun.nil,
    XRun.cons (XStep.tx fwBundle) (XRun.cons (XStep.forward hsucc) XRun.nil),
    rfl, rfl, rfl, rfl, rfl⟩
  intro c hc
  simp only [wSuccession, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨⟨by decide, by decide, trivial⟩, by simp only [Op.handsToMigration]; decide, id⟩

theorem ParkedForwardFramesFire : Properties.ParkedForwardFramesFire := by
  have hacc : FRun (wConfig false) wParked [⟨3, .ctmAcceptOwnership⟩] ⟨3, 0, 3, 35, 60, true⟩ :=
    FRun.cons (OpStep.ctmAcceptOwnership rfl) FRun.nil
  have hmig : FRun (wConfig true) wHanded [⟨9, .migrate⟩] wPost :=
    FRun.cons (OpStep.migrate fwMigratePost) FRun.nil
  exact ⟨⟨_, hacc, rfl, rfl⟩, rfl, _, hmig, rfl⟩

theorem RenounceStrandsWitness : Properties.RenounceStrandsWitness := by
  have hboth : FRun (wConfig true) wPost [⟨3, .ctmRenounceOwnership⟩, ⟨3, .paRenounceOwnership⟩]
      ⟨0, 0, 0, 35, 60, true⟩ :=
    FRun.cons (OpStep.ctmRenounceOwnership rfl)
      (FRun.cons (OpStep.paRenounceOwnership rfl) FRun.nil)
  have hctm : FRun (wConfig true) wPost [⟨3, .ctmRenounceOwnership⟩] ⟨0, 0, 3, 35, 60, true⟩ :=
    FRun.cons (OpStep.ctmRenounceOwnership rfl) FRun.nil
  have hswap : FRun (wConfig true) ⟨0, 0, 3, 35, 60, true⟩ [⟨3, .ctmCodeSwap 3 0 35 60⟩]
      ⟨3, 0, 3, 35, 60, true⟩ :=
    FRun.cons (OpStep.ctmCodeSwap rfl) FRun.nil
  refine ⟨⟨_, hboth, rfl, rfl, rfl, ?_⟩, _, _, hctm, rfl, rfl, rfl, hswap, rfl⟩
  rintro ⟨s'', h⟩
  cases h with
  | cons hstep _ =>
      cases hstep with
      | paTransferOwnership hpa _ => exact absurd hpa (by decide)

end Contracts.RegistryBootstrapMigration
