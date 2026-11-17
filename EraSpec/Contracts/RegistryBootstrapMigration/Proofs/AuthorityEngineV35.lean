import EraSpec.Contracts.RegistryBootstrapMigration.Properties.AuthorityEngineV35
import EraSpec.Contracts.RegistryBootstrapMigration.Proofs.Forward

/-!
# Proofs: the authority results survive engine legs (draft/v0.35.0)

A leg's post-checks give two facts about its end state: the executor's own owner and nominee
are the start values, and `holdersHash` takes the start value on the end holders. Either the
holders are equal, and then the hashed slots are equal entry by entry (`holders_ctm_eq`), or
they differ, and that is the collision disjunct. Nothing else is used about `holdersHash`.

The slots a leg does not check are framed by an induction over its call trace, with a
per-call frame (`vopStep_core_frame`, `vopStep_ctm_frame`).

On `AState` a call trace is one of `Forward`'s (`vrun_frun`), so the re-parking results for
call traces and core legs are `Forward`'s `frun_keeps_unparked` on the projected calls.

The countermodels and witnesses are concrete traces. Each step's end state is determined, so
"succeeds exactly when the hash agrees on the pair" is an inversion of one step
(`single_leg_iff`).
-/

namespace Contracts.RegistryBootstrapMigration

open Clear

/-! ## `setExec` -/

@[simp] lemma setExec_a (s : VState) (d : Domain) (o p : Address) : (s.setExec d o p).a = s.a := by
  cases d <;> rfl

@[simp] lemma setExec_ctmAnswers (s : VState) (d : Domain) (o p : Address) :
    (s.setExec d o p).ctmAnswers = s.ctmAnswers := by
  cases d <;> rfl

@[simp] lemma setExec_execOwner (s : VState) (d : Domain) (o p : Address) :
    (s.setExec d o p).execOwner d = o := by
  cases d <;> rfl

lemma setExec_execOwner_ne (s : VState) {d d' : Domain} (h : d' ≠ d) (o p : Address) :
    (s.setExec d o p).execOwner d' = s.execOwner d' := by
  cases d <;> cases d' <;> first | rfl | exact absurd rfl h

/-! ## A call trace is a forward on `AState` -/

lemma project_cons (c : VCall) (cs : List VCall) :
    VCall.project (c :: cs) = c.toCall.toList ++ VCall.project cs := by
  unfold VCall.project
  rw [List.filterMap_cons]
  cases c.toCall <;> rfl

/-- One call of a trace is one call of `Forward`, or leaves `AState` alone. -/
lemma vopStep_project {K : Config} {ctx : Option Domain} {a : Address} {s s' : VState}
    {op : VOp} (h : VOpStep K ctx a s op s') :
    FRun K s.a (VCall.mk a op).toCall.toList s'.a := by
  cases h with
  | fwd ho _ => exact FRun.cons ho FRun.nil
  | ctmCodeSwap hpa _ => exact FRun.cons (OpStep.ctmCodeSwap hpa) FRun.nil
  | execTransferOwnership _ => rw [setExec_a]; exact FRun.nil
  | execAcceptOwnership _ => rw [setExec_a]; exact FRun.nil
  | execSlots _ _ => rw [setExec_a]; exact FRun.nil
  | ecoTransferOwnership _ _ => exact FRun.nil
  | ecoRenounceOwnership _ => exact FRun.nil
  | notifierTransferOwnership _ => exact FRun.nil
  | notifierAcceptOwnership _ => exact FRun.nil
  | notifierRenounceOwnership _ => exact FRun.nil
  | notifierChangeAdmin _ _ => exact FRun.nil
  | notifierCodeSwap _ => exact FRun.nil

lemma vrun_frun {K : Config} {ctx : Option Domain} {s s' : VState} {cs : List VCall}
    (h : VRun K ctx s cs s') : FRun K s.a (VCall.project cs) s'.a := by
  induction h with
  | nil => exact FRun.nil
  | @cons s₁ s₂ s₃ c cs hstep _ ih =>
      rw [project_cons]
      exact frun_append (vopStep_project hstep) ih

lemma project_mem {cs : List VCall} {c : Call} (h : c ∈ VCall.project cs) :
    ∃ c' ∈ cs, c'.toCall = some c := by
  unfold VCall.project at h
  exact List.mem_filterMap.mp h

/-- A projected call hands authority to the migration, or replaces the CTM's code, only if
the call it comes from does. -/
lemma toCall_props {K : Config} {c' : VCall} {c : Call} (h : c'.toCall = some c) :
    (c.op.handsToMigration K → c'.op.handsToMigration K) ∧
      (c.op.swapsCtmCode → c'.op.swapsCtmCode) := by
  obtain ⟨a, op⟩ := c'
  cases op with
  | fwd op =>
      have hc : c = ⟨a, op⟩ := (Option.some.inj h).symm
      subst hc
      exact ⟨id, id⟩
  | ctmCodeSwap o p v r ans =>
      have hc : c = ⟨a, .ctmCodeSwap o p v r⟩ := (Option.some.inj h).symm
      subst hc
      exact ⟨fun h' => h'.elim, fun _ => trivial⟩
  | execTransferOwnership d x => exact nomatch h
  | execAcceptOwnership d => exact nomatch h
  | execRenounceOwnership d => exact nomatch h
  | execSlots d o p => exact nomatch h
  | ecoTransferOwnership x => exact nomatch h
  | ecoRenounceOwnership => exact nomatch h
  | notifierTransferOwnership x => exact nomatch h
  | notifierAcceptOwnership => exact nomatch h
  | notifierRenounceOwnership => exact nomatch h
  | notifierChangeAdmin x => exact nomatch h
  | notifierCodeSwap o p => exact nomatch h

/-! ## What a trace keeps -/

/-- A call from a spent state leaves it spent. -/
lemma opStep_spent {K : Config} {a : Address} {s s' : AState} {op : Op}
    (hx : s.executed = true) (h : OpStep K a s op s') : s'.executed = true := by
  cases h with
  | migrate hm =>
      have := (migrate_guards hm).1
      rw [hx] at this
      exact Bool.noConfusion this
  | ctmTransferOwnership _ => exact hx
  | ctmAcceptOwnership _ => exact hx
  | ctmRenounceOwnership _ => exact hx
  | ctmSetVersion _ => exact hx
  | paTransferOwnership _ _ => exact hx
  | paRenounceOwnership _ => exact hx
  | ctmCodeSwap _ => exact hx
  | untracked => exact hx

lemma frun_spent {K : Config} {s s' : AState} {cs : List Call} (h : FRun K s cs s') :
    s.executed = true → s'.executed = true := by
  induction h with
  | nil => exact id
  | cons hstep _ ih => exact fun hx => ih (opStep_spent hx hstep)

/-- The CTM keeps answering its ownership reads from its slots unless a call swaps in code
that answers them falsely. -/
lemma vopStep_answers {K : Config} {ctx : Option Domain} {a : Address} {s s' : VState}
    {op : VOp} (h : VOpStep K ctx a s op s') (hc : ¬ op.answersFalsely)
    (ha : s.ctmAnswers = none) : s'.ctmAnswers = none := by
  cases h with
  | fwd _ _ => exact ha
  | @ctmCodeSwap o p v r ans _ _ =>
      cases ans with
      | none => rfl
      | some x => exact absurd trivial hc
  | execTransferOwnership _ => rw [setExec_ctmAnswers]; exact ha
  | execAcceptOwnership _ => rw [setExec_ctmAnswers]; exact ha
  | execSlots _ _ => rw [setExec_ctmAnswers]; exact ha
  | ecoTransferOwnership _ _ => exact ha
  | ecoRenounceOwnership _ => exact ha
  | notifierTransferOwnership _ => exact ha
  | notifierAcceptOwnership _ => exact ha
  | notifierRenounceOwnership _ => exact ha
  | notifierChangeAdmin _ _ => exact ha
  | notifierCodeSwap _ => exact ha

lemma vrun_answers {K : Config} {ctx : Option Domain} {s s' : VState} {cs : List VCall}
    (h : VRun K ctx s cs s') :
    (∀ c ∈ cs, ¬ c.op.answersFalsely) → s.ctmAnswers = none → s'.ctmAnswers = none := by
  induction h with
  | nil => exact fun _ ha => ha
  | cons hstep _ ih =>
      exact fun hc ha => ih (fun c h' => hc c (List.mem_cons_of_mem _ h'))
        (vopStep_answers hstep (hc _ List.mem_cons_self) ha)

lemma answersFalsely_swaps {op : VOp} (h : op.answersFalsely) : op.swapsCtmCode := by
  cases op with
  | ctmCodeSwap o p v r ans => trivial
  | fwd op => exact h.elim
  | execTransferOwnership d x => exact h.elim
  | execAcceptOwnership d => exact h.elim
  | execRenounceOwnership d => exact h.elim
  | execSlots d o p => exact h.elim
  | ecoTransferOwnership x => exact h.elim
  | ecoRenounceOwnership => exact h.elim
  | notifierTransferOwnership x => exact h.elim
  | notifierAcceptOwnership => exact h.elim
  | notifierRenounceOwnership => exact h.elim
  | notifierChangeAdmin x => exact h.elim
  | notifierCodeSwap o p => exact h.elim

/-- A trace with no ownership call naming the migration and no CTM code swap, from a spent
state with nothing parked: `Forward`'s `frun_keeps_unparked` on the projected calls. -/
lemma vrun_keeps_unparked {K : Config} {ctx : Option Domain} {s s' : VState}
    {cs : List VCall} (h : VRun K ctx s cs s')
    (hc : ∀ c ∈ cs, ¬ c.op.handsToMigration K ∧ ¬ c.op.swapsCtmCode)
    (hx : s.a.executed = true) (hp : ¬ ParkedOnMigration K s.a) (ha : s.ctmAnswers = none) :
    s'.a.executed = true ∧ ¬ ParkedOnMigration K s'.a ∧ s'.ctmAnswers = none := by
  have hproj : ∀ c ∈ VCall.project cs, ¬ c.op.handsToMigration K ∧ ¬ c.op.swapsCtmCode := by
    intro c hmem
    obtain ⟨c', hc', hto⟩ := project_mem hmem
    obtain ⟨h1, h2⟩ := toCall_props (K := K) hto
    exact ⟨fun h' => (hc c' hc').1 (h1 h'), fun h' => (hc c' hc').2 (h2 h')⟩
  obtain ⟨hx', hp'⟩ := frun_keeps_unparked (vrun_frun h) hx hp (fun c hm => (hproj c hm).1)
    (fun c hm => (hproj c hm).2)
  exact ⟨hx', hp', vrun_answers h (fun c hm h' => (hc c hm).2 (answersFalsely_swaps h')) ha⟩

/-! ## The frame for the domain a leg does not check -/

/-- One call of a CTM leg, sent by none of the core domain's holders. -/
lemma vopStep_core_frame {K : Config} {a : Address} {s s' : VState} {op : VOp}
    (h : VOpStep K (some .ctm) a s op s') (h1 : a ≠ s.ecoOwner) (h2 : a ≠ s.cOwner)
    (h3 : a ≠ s.cPending) :
    s'.ecoOwner = s.ecoOwner ∧ s'.cOwner = s.cOwner ∧ s'.cPending = s.cPending := by
  cases h with
  | fwd _ _ => exact ⟨rfl, rfl, rfl⟩
  | ctmCodeSwap _ _ => exact ⟨rfl, rfl, rfl⟩
  | @execTransferOwnership d x ho =>
      cases d with
      | core => exact absurd ho.symm h2
      | ctm => exact ⟨rfl, rfl, rfl⟩
  | @execAcceptOwnership d hp =>
      cases d with
      | core => exact absurd hp.symm h3
      | ctm => exact ⟨rfl, rfl, rfl⟩
  | @execSlots d o p hctx _ =>
      cases d with
      | core => exact nomatch hctx
      | ctm => exact ⟨rfl, rfl, rfl⟩
  | ecoTransferOwnership ho _ => exact absurd ho.symm h1
  | ecoRenounceOwnership ho => exact absurd ho.symm h1
  | notifierTransferOwnership _ => exact ⟨rfl, rfl, rfl⟩
  | notifierAcceptOwnership _ => exact ⟨rfl, rfl, rfl⟩
  | notifierRenounceOwnership _ => exact ⟨rfl, rfl, rfl⟩
  | notifierChangeAdmin _ _ => exact ⟨rfl, rfl, rfl⟩
  | notifierCodeSwap _ => exact ⟨rfl, rfl, rfl⟩

lemma vrun_core_frame {K : Config} {s s' : VState} {cs : List VCall}
    (h : VRun K (some .ctm) s cs s') :
    (∀ c ∈ cs, c.sender ≠ s.ecoOwner ∧ c.sender ≠ s.cOwner ∧ c.sender ≠ s.cPending) →
    s'.ecoOwner = s.ecoOwner ∧ s'.cOwner = s.cOwner ∧ s'.cPending = s.cPending := by
  induction h with
  | nil => exact fun _ => ⟨rfl, rfl, rfl⟩
  | @cons s₁ s₂ s₃ c cs hstep _ ih =>
      intro hq
      obtain ⟨q1, q2, q3⟩ := hq c List.mem_cons_self
      obtain ⟨e1, e2, e3⟩ := vopStep_core_frame hstep q1 q2 q3
      obtain ⟨f1, f2, f3⟩ := ih (fun c' hc' => by
        rw [e1, e2, e3]; exact hq c' (List.mem_cons_of_mem _ hc'))
      exact ⟨f1.trans e1, f2.trans e2, f3.trans e3⟩

/-- One of `Forward`'s calls, sent by none of the CTM domain's holders and not `migrate()`. -/
lemma opStep_quiet {K : Config} {a : Address} {s s' : AState} {op : Op}
    (h : OpStep K a s op s') (h1 : a ≠ s.ctmOwner) (h2 : a ≠ s.ctmPending)
    (h3 : a ≠ s.paOwner) (h6 : op ≠ .migrate) :
    s'.ctmOwner = s.ctmOwner ∧ s'.ctmPending = s.ctmPending ∧ s'.paOwner = s.paOwner ∧
      s'.executed = s.executed := by
  cases h with
  | ctmTransferOwnership ho => exact absurd ho.symm h1
  | ctmAcceptOwnership hp => exact absurd hp.symm h2
  | ctmRenounceOwnership ho => exact absurd ho.symm h1
  | ctmSetVersion _ => exact ⟨rfl, rfl, rfl, rfl⟩
  | paTransferOwnership ho _ => exact absurd ho.symm h3
  | paRenounceOwnership ho => exact absurd ho.symm h3
  | ctmCodeSwap ho => exact absurd ho.symm h3
  | migrate _ => exact absurd rfl h6
  | untracked => exact ⟨rfl, rfl, rfl, rfl⟩

/-- One call of a core leg, sent by none of the CTM domain's holders and not `migrate()`. -/
lemma vopStep_ctm_frame {K : Config} {a : Address} {s s' : VState} {op : VOp}
    (h : VOpStep K (some .core) a s op s') (h1 : a ≠ s.a.ctmOwner) (h2 : a ≠ s.a.ctmPending)
    (h3 : a ≠ s.a.paOwner) (h4 : a ≠ s.eOwner) (h5 : a ≠ s.ePending)
    (h6 : op ≠ .fwd .migrate) :
    s'.a.ctmOwner = s.a.ctmOwner ∧ s'.a.ctmPending = s.a.ctmPending ∧
      s'.a.paOwner = s.a.paOwner ∧ s'.eOwner = s.eOwner ∧ s'.ePending = s.ePending ∧
      s'.a.executed = s.a.executed := by
  cases h with
  | fwd ho _ =>
      obtain ⟨e1, e2, e3, e4⟩ := opStep_quiet ho h1 h2 h3 (fun e => h6 (by rw [e]))
      exact ⟨e1, e2, e3, rfl, rfl, e4⟩
  | ctmCodeSwap hpa _ => exact absurd hpa.symm h3
  | @execTransferOwnership d x ho =>
      cases d with
      | core => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      | ctm => exact absurd ho.symm h4
  | @execAcceptOwnership d hp =>
      cases d with
      | core => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      | ctm => exact absurd hp.symm h5
  | @execSlots d o p hctx _ =>
      cases d with
      | core => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      | ctm => exact nomatch hctx
  | ecoTransferOwnership _ _ => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | ecoRenounceOwnership _ => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | notifierTransferOwnership _ => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | notifierAcceptOwnership _ => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | notifierRenounceOwnership _ => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | notifierChangeAdmin _ _ => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | notifierCodeSwap _ => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma vrun_ctm_frame {K : Config} {s s' : VState} {cs : List VCall}
    (h : VRun K (some .core) s cs s') :
    (∀ c ∈ cs, c.sender ≠ s.a.ctmOwner ∧ c.sender ≠ s.a.ctmPending ∧ c.sender ≠ s.a.paOwner ∧
      c.sender ≠ s.eOwner ∧ c.sender ≠ s.ePending ∧ c.op ≠ .fwd .migrate) →
    s'.a.ctmOwner = s.a.ctmOwner ∧ s'.a.ctmPending = s.a.ctmPending ∧
      s'.a.paOwner = s.a.paOwner ∧ s'.eOwner = s.eOwner ∧ s'.ePending = s.ePending ∧
      s'.a.executed = s.a.executed := by
  induction h with
  | nil => exact fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | @cons s₁ s₂ s₃ c cs hstep _ ih =>
      intro hq
      obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hq c List.mem_cons_self
      obtain ⟨e1, e2, e3, e4, e5, e6⟩ := vopStep_ctm_frame hstep q1 q2 q3 q4 q5 q6
      obtain ⟨f1, f2, f3, f4, f5, f6⟩ := ih (fun c' hc' => by
        rw [e1, e2, e3, e4, e5]; exact hq c' (List.mem_cons_of_mem _ hc'))
      exact ⟨f1.trans e1, f2.trans e2, f3.trans e3, f4.trans e4, f5.trans e5, f6.trans e6⟩

/-! ## What equal holders say -/

/-- Equal CTM-domain holders, read from a CTM that answers from its slots, are equal slots. -/
lemma holders_ctm_eq {s s' : VState} (h : s'.holders .ctm = s.holders .ctm)
    (ha : s.ctmAnswers = none) (ha' : s'.ctmAnswers = none) :
    s'.a.paOwner = s.a.paOwner ∧ s'.a.ctmOwner = s.a.ctmOwner ∧
      s'.a.ctmPending = s.a.ctmPending ∧ (s.hasNotifier = true → s'.nOwner = s.nOwner) := by
  simp only [VState.holders, VState.ctmRead, ha, ha', Option.getD_none, Holders.ctm.injEq] at h
  obtain ⟨h1, h2, h3, _, h5⟩ := h
  refine ⟨h1, h2, h3, fun hn => ?_⟩
  rw [hn] at h5
  by_cases hn' : s'.hasNotifier = true
  · rw [hn'] at h5
    simp only [if_true, Option.some.injEq, Prod.mk.injEq] at h5
    exact h5.1
  · rw [Bool.not_eq_true] at hn'
    rw [hn'] at h5
    simp at h5

lemma holders_core_eq {s s' : VState} (h : s'.holders .core = s.holders .core) :
    s'.ecoOwner = s.ecoOwner := by
  simpa [VState.holders] using h

lemma leg_run {K : Config} {H : Holders → UInt256} {d : Domain} {s s' : VState}
    {cs : List VCall} (h : EngineLeg K H d s cs s') :
    VRun K (some d) s cs s' ∧ s'.execOwner d = s.execOwner d ∧
      s'.execPending d = s.execPending d ∧ H (s'.holders d) = H (s.holders d) := by
  cases h with
  | mk hrun ho hp hH => exact ⟨hrun, ho, hp, hH⟩

/-- The leg's own domain: equal holders, or a collision on the logged pair. -/
lemma leg_own_frame {K : Config} {H : Holders → UInt256} {d : Domain} {s s' : VState}
    {cs : List VCall} (h : EngineLeg K H d s cs s')
    (hans : d = .ctm → s.ctmAnswers = none ∧ s'.ctmAnswers = none) :
    (OwnFrame d s s' ∧ s'.holders d = s.holders d) ∨ Collides H (s.holders d) (s'.holders d) := by
  obtain ⟨_, ho, hp, hH⟩ := leg_run h
  by_cases heq : s'.holders d = s.holders d
  · left
    refine ⟨?_, heq⟩
    cases d with
    | ctm =>
        obtain ⟨ha, ha'⟩ := hans rfl
        obtain ⟨h1, h2, h3, _⟩ := holders_ctm_eq heq ha ha'
        exact ⟨h2, h3, h1, ho, hp⟩
    | core => exact ⟨holders_core_eq heq, ho, hp⟩
  · exact Or.inr ⟨fun e => heq e.symm, hH.symm⟩

lemma leg_other_frame {K : Config} {H : Holders → UInt256} {d : Domain} {s s' : VState}
    {cs : List VCall} (h : EngineLeg K H d s cs s') (hq : OtherDomainQuiet d s cs) :
    OtherFrame d s s' := by
  obtain ⟨hrun, _⟩ := leg_run h
  cases d with
  | ctm => exact vrun_core_frame hrun hq
  | core => exact vrun_ctm_frame hrun hq

/-! ## Certificates: a leg can neither park nor unpark -/

theorem EngineLegKeepsItsExecutor : Properties.EngineLegKeepsItsExecutor := by
  intro K H d s s' cs h
  obtain ⟨_, ho, hp, _⟩ := leg_run h
  exact ⟨ho, hp⟩

theorem EngineLegOtherDomainFrame : Properties.EngineLegOtherDomainFrame :=
  fun _ _ _ _ _ _ h hq => leg_other_frame h hq

theorem EngineLegOwnDomainFrameOrCollision : Properties.EngineLegOwnDomainFrameOrCollision :=
  fun _ _ _ _ _ _ h hans => leg_own_frame h hans

theorem EngineLegFrameOrCollision : Properties.EngineLegFrameOrCollision := by
  intro K H d s s' cs h hq hans
  rcases leg_own_frame h hans with ⟨hown, heq⟩ | hcol
  · left
    refine ⟨?_, heq⟩
    have hother := leg_other_frame h hq
    cases d with
    | ctm =>
        obtain ⟨o1, o2, o3, o4, o5⟩ := hown
        obtain ⟨p1, p2, p3⟩ := hother
        exact ⟨o1, o2, o3, p1, o4, o5, p2, p3⟩
    | core =>
        obtain ⟨o1, o2, o3⟩ := hown
        obtain ⟨p1, p2, p3, p4, p5, _⟩ := hother
        exact ⟨p1, p2, p3, o1, p4, p5, o2, o3⟩
  · exact Or.inr hcol

theorem EngineLegNeitherParksNorUnparks : Properties.EngineLegNeitherParksNorUnparks := by
  intro K H d s s' cs h hans hq
  have hiff : s'.a.ctmOwner = s.a.ctmOwner → s'.a.ctmPending = s.a.ctmPending →
      s'.a.paOwner = s.a.paOwner → (ParkedOnMigration K s'.a ↔ ParkedOnMigration K s.a) := by
    intro e1 e2 e3
    unfold ParkedOnMigration
    rw [e1, e2, e3]
  cases d with
  | ctm =>
      rcases leg_own_frame h hans with ⟨⟨o1, o2, o3, _, _⟩, _⟩ | hcol
      · exact Or.inl (hiff o1 o2 o3)
      · exact Or.inr hcol
  | core =>
      obtain ⟨p1, p2, p3, _⟩ := leg_other_frame h (hq rfl)
      exact Or.inl (hiff p1 p2 p3)

/-! ## Certificates: a leg's calls are a forward -/

theorem CallTracesAreForwards : Properties.CallTracesAreForwards :=
  fun _ _ _ _ _ h => ⟨vrun_frun h, fun _ hc => project_mem hc⟩

theorem EngineLegCallsAreAForward : Properties.EngineLegCallsAreAForward :=
  fun _ _ _ _ _ _ h => vrun_frun (leg_run h).1

/-- One transaction from a spent state with nothing parked and a CTM that answers from its
slots keeps all three, or it is a leg whose hash collides on its logged pair. -/
lemma vsysStep_keeps_unparked {K : Config} {H : Holders → UInt256} {s s' : VState}
    {v : VLabel} (h : VSysStep K H s v s') (hv : v.Clean K) (hx : s.a.executed = true)
    (hp : ¬ ParkedOnMigration K s.a) (ha : s.ctmAnswers = none) :
    (s'.a.executed = true ∧ ¬ ParkedOnMigration K s'.a ∧ s'.ctmAnswers = none) ∨
      ∃ (d : Domain) (cs : List VCall), v = .engineLeg d cs ∧ EngineLeg K H d s cs s' ∧
        Collides H (s.holders d) (s'.holders d) := by
  cases h with
  | tx hstep =>
      obtain ⟨hx', hp'⟩ := astep_keeps_unparked hx hp hv hstep
      exact Or.inl ⟨hx', hp', ha⟩
  | call hrun => exact Or.inl (vrun_keeps_unparked hrun hv hx hp ha)
  | @engineLeg _ d cs hleg =>
      cases d with
      | core => exact Or.inl (vrun_keeps_unparked (leg_run hleg).1 hv hx hp ha)
      | ctm =>
          have hrun := (leg_run hleg).1
          have ha' : s'.ctmAnswers = none := vrun_answers hrun hv ha
          have hx' : s'.a.executed = true := frun_spent (vrun_frun hrun) hx
          rcases leg_own_frame hleg (fun _ => ⟨ha, ha'⟩) with ⟨⟨o1, o2, o3, _, _⟩, _⟩ | hcol
          · refine Or.inl ⟨hx', ?_, ha'⟩
            unfold ParkedOnMigration at hp ⊢
            rw [o1, o2, o3]
            exact hp
          · exact Or.inr ⟨.ctm, cs, rfl, hleg, hcol⟩

lemma vsysRun_keeps_unparked {K : Config} {H : Holders → UInt256} {s s' : VState}
    {vs : List VLabel} (h : VSysRun K H s vs s') :
    s.a.executed = true → ¬ ParkedOnMigration K s.a → s.ctmAnswers = none →
    (∀ v ∈ vs, v.Clean K) →
    ¬ ParkedOnMigration K s'.a ∨
      ∃ (d : Domain) (cs : List VCall) (t t' : VState), VLabel.engineLeg d cs ∈ vs ∧
        EngineLeg K H d t cs t' ∧ Collides H (t.holders d) (t'.holders d) := by
  induction h with
  | nil => exact fun _ hp _ _ => Or.inl hp
  | @cons s₁ s₂ s₃ v vs hstep _ ih =>
      intro hx hp ha hc
      rcases vsysStep_keeps_unparked hstep (hc v List.mem_cons_self) hx hp ha with
        ⟨hx2, hp2, ha2⟩ | ⟨d, cs, hv, hl, hcol⟩
      · rcases ih hx2 hp2 ha2 (fun v' h' => hc v' (List.mem_cons_of_mem _ h')) with
          hfin | ⟨d, cs, t, t', hm, hl, hcol⟩
        · exact Or.inl hfin
        · exact Or.inr ⟨d, cs, t, t', List.mem_cons_of_mem _ hm, hl, hcol⟩
      · exact Or.inr ⟨d, cs, s₁, s₂, hv ▸ List.mem_cons_self, hl, hcol⟩

theorem NoReparkingAcrossEngineLegs : Properties.NoReparkingAcrossEngineLegs :=
  fun _ _ _ _ _ hx hp ha h hc => vsysRun_keeps_unparked h hx hp ha hc

theorem MigrateLeavesNothingParkedWithEngineLegs :
    Properties.MigrateLeavesNothingParkedWithEngineLegs := by
  intro K H t s s' vs hgen hm ha h hc
  obtain ⟨_, _, _, hnp, _⟩ := MigrateLeavesNothingParked K t s.a hgen hm
  exact vsysRun_keeps_unparked h (MigrateIsOneShot K t s.a hm).1 hnp ha hc

/-! ## Certificates: the engine inside its executor -/

theorem EngineReachesOnlyAcceptCTMOwnership : Properties.EngineReachesOnlyAcceptCTMOwnership := by
  refine ⟨?_, fun K s chainAdmin h => Or.inr h.symm⟩
  intro K d s chainAdmin e hdecl ho hp hca hg
  cases e with
  | forward => exact absurd hg.symm ho
  | applyInfrastructureUpgrade => exact absurd hg.symm ho
  | applyCTMUpgrade => exact absurd hg.symm ho
  | applyL1Upgrade => exact absurd hg.symm ho
  | upgradeChain id =>
      rcases hg with hg | hg
      · exact absurd hg.symm ho
      · exact absurd hg.symm (hca id)
  | acceptCTMOwnership =>
      rcases hg with hg | hg
      · exact absurd hg.symm ho
      · cases d with
        | core => exact hdecl.elim
        | ctm => exact ⟨rfl, rfl, hg.symm⟩
  | transferOwnership x => exact absurd hg.symm ho
  | acceptOwnership => exact absurd hg.symm hp
  | renounceOwnership => exact hg.elim

/-- One call by a nonzero sender keeps a nonzero owner on every executor whose storage the
running code does not share. -/
lemma vopStep_execOwner_ne_zero {K : Config} {ctx : Option Domain} {a : Address}
    {s s' : VState} {op : VOp} (h : VOpStep K ctx a s op s') (ha : a ≠ 0) (d' : Domain)
    (hctx : ctx ≠ some d') (h0 : s.execOwner d' ≠ 0) : s'.execOwner d' ≠ 0 := by
  cases h with
  | fwd _ _ => exact h0
  | ctmCodeSwap _ _ => exact h0
  | @execTransferOwnership d x ho =>
      by_cases hd : d' = d
      · subst hd; rw [setExec_execOwner]; exact h0
      · rw [setExec_execOwner_ne _ hd]; exact h0
  | @execAcceptOwnership d hp =>
      by_cases hd : d' = d
      · subst hd; rw [setExec_execOwner]; exact ha
      · rw [setExec_execOwner_ne _ hd]; exact h0
  | @execSlots d o p hc _ =>
      by_cases hd : d' = d
      · subst hd; exact absurd hc hctx
      · rw [setExec_execOwner_ne _ hd]; exact h0
  | ecoTransferOwnership _ _ => exact h0
  | ecoRenounceOwnership _ => exact h0
  | notifierTransferOwnership _ => exact h0
  | notifierAcceptOwnership _ => exact h0
  | notifierRenounceOwnership _ => exact h0
  | notifierChangeAdmin _ _ => exact h0
  | notifierCodeSwap _ => exact h0

lemma vrun_execOwner_ne_zero {K : Config} {ctx : Option Domain} {s s' : VState}
    {cs : List VCall} (h : VRun K ctx s cs s') (d' : Domain) (hctx : ctx ≠ some d') :
    (∀ c ∈ cs, c.sender ≠ 0) → s.execOwner d' ≠ 0 → s'.execOwner d' ≠ 0 := by
  induction h with
  | nil => exact fun _ h0 => h0
  | cons hstep _ ih =>
      exact fun hs h0 => ih (fun c hc => hs c (List.mem_cons_of_mem _ hc))
        (vopStep_execOwner_ne_zero hstep (hs _ List.mem_cons_self) d' hctx h0)

lemma vsysStep_execOwner_ne_zero {K : Config} {H : Holders → UInt256} {s s' : VState}
    {v : VLabel} (h : VSysStep K H s v s') (hs : v.SendersNonzero) (d' : Domain)
    (h0 : s.execOwner d' ≠ 0) : s'.execOwner d' ≠ 0 := by
  cases h with
  | tx _ => exact h0
  | call hrun => exact vrun_execOwner_ne_zero hrun d' (fun h => nomatch h) hs h0
  | @engineLeg _ d cs hleg =>
      obtain ⟨hrun, ho, _⟩ := leg_run hleg
      by_cases hd : d' = d
      · subst hd; rw [ho]; exact h0
      · exact vrun_execOwner_ne_zero hrun d' (fun h => hd (Option.some.inj h).symm) hs h0

lemma vsysRun_execOwner_ne_zero {K : Config} {H : Holders → UInt256} {s s' : VState}
    {vs : List VLabel} (h : VSysRun K H s vs s') (d' : Domain) :
    (∀ v ∈ vs, v.SendersNonzero) → s.execOwner d' ≠ 0 → s'.execOwner d' ≠ 0 := by
  induction h with
  | nil => exact fun _ h0 => h0
  | cons hstep _ ih =>
      exact fun hs h0 => ih (fun v hv => hs v (List.mem_cons_of_mem _ hv))
        (vsysStep_execOwner_ne_zero hstep (hs _ List.mem_cons_self) d' h0)

lemma no_execRenounce (K : Config) (ctx : Option Domain) (a : Address) (s t : VState)
    (d : Domain) : ¬ VOpStep K ctx a s (.execRenounceOwnership d) t :=
  fun h => nomatch h

theorem ExecutorOwnerNeverZero : Properties.ExecutorOwnerNeverZero := by
  refine ⟨?_, ?_, no_execRenounce, ?_⟩
  · intro o own p h
    cases h with
    | mk ho => exact ho
  · intro own p h
    cases h with
    | mk ho => exact ho rfl
  · intro K H s s' vs h hs he hc
    exact ⟨vsysRun_execOwner_ne_zero h .ctm hs he, vsysRun_execOwner_ne_zero h .core hs hc⟩

/-! ## Inversions of single calls -/

lemma vrun_single {K : Config} {ctx : Option Domain} {s s' : VState} {a : Address} {op : VOp}
    (h : VRun K ctx s [⟨a, op⟩] s') : VOpStep K ctx a s op s' := by
  cases h with
  | cons hstep hnil =>
      cases hnil
      exact hstep

lemma vopStep_fwd {K : Config} {ctx : Option Domain} {s s' : VState} {a : Address} {op : Op}
    (h : VOpStep K ctx a s (.fwd op) s') : ∃ t, OpStep K a s.a op t ∧ s' = { s with a := t } := by
  cases h with
  | fwd ho _ => exact ⟨_, ho, rfl⟩

lemma opStep_paTransfer {K : Config} {a x : Address} {s t : AState}
    (h : OpStep K a s (.paTransferOwnership x) t) : t = { s with paOwner := x } := by
  cases h with
  | paTransferOwnership _ _ => rfl

lemma opStep_ctmTransfer {K : Config} {a x : Address} {s t : AState}
    (h : OpStep K a s (.ctmTransferOwnership x) t) : t = { s with ctmPending := x } := by
  cases h with
  | ctmTransferOwnership _ => rfl

lemma opStep_ctmAccept {K : Config} {a : Address} {s t : AState}
    (h : OpStep K a s .ctmAcceptOwnership t) : t = { s with ctmOwner := a, ctmPending := 0 } := by
  cases h with
  | ctmAcceptOwnership _ => rfl

lemma opStep_ctmRenounce {K : Config} {a : Address} {s t : AState}
    (h : OpStep K a s .ctmRenounceOwnership t) : t = { s with ctmOwner := 0, ctmPending := 0 } := by
  cases h with
  | ctmRenounceOwnership _ => rfl

/-- A one-call CTM leg whose call leaves `t` succeeds exactly when the hash agrees on the
logged pair, provided the call's end state is determined and keeps the executor's slots. -/
lemma single_leg_iff {K : Config} {H : Holders → UInt256} {s t : VState} {a : Address}
    {op : VOp} (hstep : VOpStep K (some .ctm) a s op t)
    (hdet : ∀ s', VOpStep K (some .ctm) a s op s' → s' = t)
    (ho : t.eOwner = s.eOwner) (hp : t.ePending = s.ePending) :
    (∃ s', EngineLeg K H .ctm s [⟨a, op⟩] s') ↔ H (s.holders .ctm) = H (t.holders .ctm) := by
  constructor
  · rintro ⟨s', hleg⟩
    obtain ⟨hrun, _, _, hH⟩ := leg_run hleg
    rw [hdet s' (vrun_single hrun)] at hH
    exact hH.symm
  · intro hH
    exact ⟨t, EngineLeg.mk (VRun.cons hstep VRun.nil) ho hp hH.symm⟩

/-! ## Certificates: (c), (d) and the countermodels -/

private lemma not_parked_postV : ¬ ParkedOnMigration (wConfig true) wPostV.a := by
  unfold ParkedOnMigration; decide

theorem LegCannotRecoverParkedCTM : Properties.LegCannotRecoverParkedCTM := by
  have hstep : ∀ ctx, VOpStep (wConfig false) ctx 3 wParkedV (.fwd .ctmAcceptOwnership)
      wRecoveredV := fun ctx => VOpStep.fwd (OpStep.ctmAcceptOwnership rfl) id
  refine ⟨?_, ⟨wRecoveredV, VRun.cons (hstep none) VRun.nil, rfl, rfl, ?_⟩, ?_, by decide⟩
  · intro H s s' cs hs ha ha' hleg
    rcases leg_own_frame hleg (fun _ => ⟨ha, ha'⟩) with ⟨⟨o1, o2, _, _, _⟩, _⟩ | hcol
    · left
      have h1 : s'.a.ctmOwner = 50 := by rw [o1, hs]; rfl
      have h2 : s'.a.ctmPending = 3 := by rw [o2, hs]; rfl
      exact ⟨h1, h2, Or.inl h1⟩
    · exact Or.inr hcol
  · unfold ParkedOnMigration; decide
  · intro H
    refine single_leg_iff (hstep _) ?_ rfl rfl
    intro s' h
    obtain ⟨t, ht, rfl⟩ := vopStep_fwd h
    rw [opStep_ctmAccept ht]
    rfl

theorem LegRenounceReverts : Properties.LegRenounceReverts := by
  have hstep : ∀ ctx, VOpStep (wConfig true) ctx 3 wPostV (.fwd .ctmRenounceOwnership)
      wCtmRenouncedV := fun ctx => VOpStep.fwd (OpStep.ctmRenounceOwnership rfl) id
  refine ⟨?_, ?_, no_execRenounce, ?_, by decide,
    ⟨wCtmRenouncedV, VRun.cons (hstep none) VRun.nil, rfl, rfl⟩⟩
  · intro K H s s' cs hleg ha ha' h1 h2
    by_cases heq : s'.holders .ctm = s.holders .ctm
    · left
      obtain ⟨e1, e2, _, e4⟩ := holders_ctm_eq heq ha ha'
      exact ⟨by rw [e2]; exact h1, by rw [e1]; exact h2, fun hn h3 => by rw [e4 hn]; exact h3⟩
    · exact Or.inr ⟨fun e => heq e.symm, (leg_run hleg).2.2.2.symm⟩
  · intro K H s s' cs hleg h1
    rcases leg_own_frame hleg (fun h => nomatch h) with ⟨⟨o1, _, _⟩, _⟩ | hcol
    · exact Or.inl (by rw [o1]; exact h1)
    · exact Or.inr hcol
  · intro H
    refine single_leg_iff (hstep _) ?_ rfl rfl
    intro s' h
    obtain ⟨t, ht, rfl⟩ := vopStep_fwd h
    rw [opStep_ctmRenounce ht]
    rfl

theorem CollisionDisjunctNeeded : Properties.CollisionDisjunctNeeded := by
  have hstep : VOpStep (wConfig true) (some .ctm) 3 wPostV (.fwd (.paTransferOwnership 7))
      wPaMovedV := VOpStep.fwd (OpStep.paTransferOwnership rfl (by decide)) id
  refine ⟨?_, by decide, ?_, rfl, rfl,
    ⟨fun _ => 0, wPaMovedV, EngineLeg.mk (VRun.cons hstep VRun.nil) rfl rfl rfl, rfl, ?_⟩⟩
  · intro H
    refine single_leg_iff hstep ?_ rfl rfl
    intro s' h
    obtain ⟨t, ht, rfl⟩ := vopStep_fwd h
    rw [opStep_paTransfer ht]
    rfl
  · intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    exact ⟨by decide, by decide, by decide⟩
  · rintro ⟨_, _, h3, _⟩
    exact absurd h3 (by decide)

theorem NoHolderCheckReparks : Properties.NoHolderCheckReparks := by
  have hstep : VOpStep (wConfig true) (some .ctm) 3 wPostV (.fwd (.ctmTransferOwnership 50))
      wNominatedV := VOpStep.fwd (OpStep.ctmTransferOwnership rfl) id
  refine ⟨rfl, not_parked_postV,
    EngineLegNoHolderCheck.mk (VRun.cons hstep VRun.nil) rfl rfl, Or.inr (Or.inl rfl), ?_,
    by decide⟩
  intro H
  refine single_leg_iff hstep ?_ rfl rfl
  intro s' h
  obtain ⟨t, ht, rfl⟩ := vopStep_fwd h
  rw [opStep_ctmTransfer ht]
  rfl

theorem EngineCtmSwapReparks : Properties.EngineCtmSwapReparks := by
  refine ⟨rfl, not_parked_postV, ?_, ?_⟩
  · intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    exact id
  · intro H
    exact ⟨_, EngineLeg.mk (VRun.cons (VOpStep.ctmCodeSwap rfl rfl) VRun.nil) rfl rfl rfl, rfl,
      Or.inl rfl, fun h => nomatch h⟩

private lemma veAuth : ExecutorAuthorities (wConfig true) :=
  ⟨⟨9, 0, 1, 2, true⟩, ⟨9, 0, 0, 0, true⟩, by simp [wConfig, wExec, wManifest],
    by simp [wConfig, wExec, wManifest], rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private lemma veMigratePost : MigrateStep (wConfig true) wHanded wPost := by
  have hcomp : executorAccept (wConfig true) (handOn (wConfig true)
      (claim (wConfig true) wHanded)) = wPost := by decide
  exact hcomp ▸ MigrateStep.mk rfl (by decide) rfl veAuth rfl rfl (by decide) (by decide)

theorem CoreLegMayRunMigrate : Properties.CoreLegMayRunMigrate := by
  intro H
  have hstep : VOpStep (wConfig true) (some .core) 4 wHandedV (.fwd .migrate) wPostV :=
    VOpStep.fwd (OpStep.migrate veMigratePost) id
  exact ⟨wPostV, EngineLeg.mk (VRun.cons hstep VRun.nil) rfl rfl rfl, by decide, by decide,
    not_parked_postV⟩

theorem OtherDomainQuietNeeded : Properties.OtherDomainQuietNeeded := by
  refine ⟨?_, ?_⟩
  · intro h
    exact (h _ List.mem_cons_self).1 rfl
  · intro H
    refine ⟨_, EngineLeg.mk (VRun.cons (VOpStep.ecoTransferOwnership rfl (by decide)) VRun.nil)
      rfl rfl rfl, rfl, rfl, ?_⟩
    rintro ⟨_, _, _, h4, _⟩
    exact absurd h4 (by decide)

theorem UnnamedNotifierIsUnchecked : Properties.UnnamedNotifierIsUnchecked := by
  refine ⟨?_, ?_, by decide⟩
  · intro H
    exact ⟨_, EngineLeg.mk (VRun.cons (VOpStep.notifierRenounceOwnership rfl) VRun.nil)
      rfl rfl rfl, rfl, by decide, rfl⟩
  · intro H
    refine single_leg_iff (VOpStep.notifierRenounceOwnership rfl) ?_ rfl rfl
    intro s' h
    cases h with
    | notifierRenounceOwnership _ => rfl

theorem EngineGatePremisesNeeded : Properties.EngineGatePremisesNeeded := by
  refine ⟨fun K d s chainAdmin h => h.symm, fun K s chainAdmin id h => Or.inr h.symm, ?_⟩
  intro H
  have h1 : VOpStep (wConfig true) (some .ctm) 3 wPostV (.execSlots .ctm 3 0)
      (wPostV.setExec .ctm 3 0) := VOpStep.execSlots rfl rfl
  have h2 : VOpStep (wConfig true) (some .ctm) 3 (wPostV.setExec .ctm 3 0) (.execSlots .ctm 9 0)
      wPostV := VOpStep.execSlots rfl rfl
  exact ⟨EngineLeg.mk (VRun.cons h1 (VRun.cons h2 VRun.nil)) rfl rfl rfl,
    VRun.cons h1 VRun.nil⟩

/-! ## Witness -/

theorem EngineLegTransientWitness : Properties.EngineLegTransientWitness := by
  have s1 : VOpStep (wConfig true) (some .ctm) 3 wPostV (.fwd (.ctmTransferOwnership 7))
      { wPostV with a := ⟨3, 7, 3, 35, 60, true⟩ } :=
    VOpStep.fwd (OpStep.ctmTransferOwnership rfl) id
  have s2 : VOpStep (wConfig true) (some .ctm) 7 { wPostV with a := ⟨3, 7, 3, 35, 60, true⟩ }
      (.fwd .ctmAcceptOwnership) { wPostV with a := ⟨7, 0, 3, 35, 60, true⟩ } :=
    VOpStep.fwd (OpStep.ctmAcceptOwnership rfl) id
  have s3 : VOpStep (wConfig true) (some .ctm) 7 { wPostV with a := ⟨7, 0, 3, 35, 60, true⟩ }
      (.fwd (.ctmTransferOwnership 3)) { wPostV with a := ⟨7, 3, 3, 35, 60, true⟩ } :=
    VOpStep.fwd (OpStep.ctmTransferOwnership rfl) id
  have s4 : VOpStep (wConfig true) (some .ctm) 3 { wPostV with a := ⟨7, 3, 3, 35, 60, true⟩ }
      (.fwd .ctmAcceptOwnership) wPostV :=
    VOpStep.fwd (OpStep.ctmAcceptOwnership rfl) id
  have hrun : VRun (wConfig true) (some .ctm) wPostV wTransient wPostV :=
    VRun.cons s1 (VRun.cons s2 (VRun.cons s3 (VRun.cons s4 VRun.nil)))
  have hleg : ∀ H : Holders → UInt256, EngineLeg (wConfig true) H .ctm wPostV wTransient wPostV :=
    fun H => EngineLeg.mk hrun rfl rfl rfl
  have hcore : ∀ H : Holders → UInt256,
      EngineLeg (wConfig true) H .core wPostV [⟨4, .fwd .untracked⟩] wPostV :=
    fun H => EngineLeg.mk (VRun.cons (VOpStep.fwd OpStep.untracked id) VRun.nil) rfl rfl rfl
  have hquiet : OtherDomainQuiet .ctm wPostV wTransient := by
    intro c hc
    simp only [wTransient, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩
  refine ⟨hleg, ⟨_, VRun.cons s1 (VRun.cons s2 VRun.nil), rfl⟩, hquiet, rfl, rfl,
    not_parked_postV, by decide, by decide, ?_⟩
  intro H
  refine ⟨VSysRun.cons (VSysStep.engineLeg (hleg H))
    (VSysRun.cons (VSysStep.engineLeg (hcore H)) VSysRun.nil), ?_, ?_⟩
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · refine ⟨?_, ?_⟩
      · intro c hc
        simp only [wTransient, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> exact id
      · intro c hc
        simp only [wTransient, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> decide
    · refine ⟨?_, ?_⟩
      · intro c hc
        rw [List.mem_singleton] at hc
        subst hc
        exact ⟨id, id⟩
      · intro c hc
        rw [List.mem_singleton] at hc
        subst hc
        decide
  · intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    exact ⟨by decide, by decide, by decide, by decide, by decide, fun h => nomatch h⟩

end Contracts.RegistryBootstrapMigration
