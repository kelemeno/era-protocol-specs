import EraSpec.Contracts.RegistryBootstrapMigration.Properties.AuthorityEngineV35
import EraSpec.Contracts.RegistryBootstrapMigration.Proofs.Forward

/-!
# Proofs: the authority results across engine legs (draft/v0.35.0)

A leg's post-checks give two facts about its end state: the executor's own owner and nominee
are the start values, and `holdersHash` takes the start value on the end holders. Either the
holders are equal, and then the hashed reads are equal entry by entry
(`engineV35_holders_ctm_inj`), or they differ, and that is the collision disjunct. Nothing else
is used about `holdersHash`.

The slots a leg does not check are framed by an induction over its call trace, with a
per-call frame (`engineV35_vopStep_core_frame`, `engineV35_vopStep_ctm_frame`).

On `AState` a call trace is one of `Forward`'s (`engineV35_vrun_frun`), so the re-parking
results for call traces and core legs are `Forward`'s `frun_keeps_unparked` on the projected
calls. Along a run, the first transaction that breaks the invariant is a colliding leg, and the
run splits there (`RunLegCollides`).

The countermodels and witnesses are concrete traces. Every call has one outcome
(`engineV35_vrun_det`), so "succeeds exactly when the hash agrees on the pair" is an inversion
of the trace (`engineV35_leg_iff`).
-/

namespace Contracts.RegistryBootstrapMigration

open Clear

/-! ## `setExec` -/

@[simp] lemma engineV35_setExec_a (s : VState) (d : LegDomain) (o p : Address) :
    (s.setExec d o p).a = s.a := by
  cases d <;> rfl

@[simp] lemma engineV35_setExec_ctmAnswers (s : VState) (d : LegDomain) (o p : Address) :
    (s.setExec d o p).ctmAnswers = s.ctmAnswers := by
  cases d <;> rfl

@[simp] lemma engineV35_setExec_execOwner (s : VState) (d : LegDomain) (o p : Address) :
    (s.setExec d o p).execOwner d = o := by
  cases d <;> rfl

lemma engineV35_setExec_execOwner_ne (s : VState) {d d' : LegDomain} (h : d' ≠ d)
    (o p : Address) : (s.setExec d o p).execOwner d' = s.execOwner d' := by
  cases d <;> cases d' <;> first | rfl | exact absurd rfl h

/-! ## Every call has one outcome -/

lemma engineV35_opStep_det {K : Config} {a : Address} {s t₁ t₂ : AState} {op : Op}
    (h₁ : OpStep K a s op t₁) (h₂ : OpStep K a s op t₂) : t₁ = t₂ := by
  cases h₁ with
  | migrate hm =>
      cases h₂ with
      | migrate hm' => rw [migrate_eq hm, migrate_eq hm']
  | ctmTransferOwnership _ => cases h₂; rfl
  | ctmAcceptOwnership _ => cases h₂; rfl
  | ctmRenounceOwnership _ => cases h₂; rfl
  | ctmSetVersion _ => cases h₂; rfl
  | paTransferOwnership _ _ => cases h₂; rfl
  | paRenounceOwnership _ => cases h₂; rfl
  | ctmCodeSwap _ => cases h₂; rfl
  | untracked => cases h₂; rfl

lemma engineV35_vopStep_det {K : Config} {ctx : Option LegDomain} {a : Address}
    {s t₁ t₂ : VState} {op : VOp} (h₁ : VOpStep K ctx a s op t₁) (h₂ : VOpStep K ctx a s op t₂) :
    t₁ = t₂ := by
  cases h₁ with
  | fwd ho _ =>
      cases h₂ with
      | fwd ho' _ => rw [engineV35_opStep_det ho ho']
  | ctmCodeSwap _ _ => cases h₂; rfl
  | ctmSetPendingAdmin _ => cases h₂; rfl
  | ctmAcceptAdmin _ => cases h₂; rfl
  | ctmSetServerNotifier _ => cases h₂; rfl
  | execTransferOwnership _ => cases h₂; rfl
  | execAcceptOwnership _ => cases h₂; rfl
  | execSlots _ _ => cases h₂; rfl
  | ecoTransferOwnership _ _ => cases h₂; rfl
  | ecoRenounceOwnership _ => cases h₂; rfl
  | notifierTransferOwnership _ => cases h₂; rfl
  | notifierAcceptOwnership _ => cases h₂; rfl
  | notifierRenounceOwnership _ => cases h₂; rfl
  | notifierSetChainTypeManager _ _ => cases h₂; rfl
  | notifierChangeAdmin _ _ => cases h₂; rfl
  | notifierCodeSwap _ => cases h₂; rfl

lemma engineV35_vrun_det {K : Config} {ctx : Option LegDomain} {s t₁ t₂ : VState}
    {cs : List VCall} (h₁ : VRun K ctx s cs t₁) (h₂ : VRun K ctx s cs t₂) : t₁ = t₂ := by
  induction h₁ generalizing t₂ with
  | nil => cases h₂; rfl
  | cons hstep _ ih =>
      cases h₂ with
      | cons hstep' hrest' =>
          rw [engineV35_vopStep_det hstep hstep'] at ih
          exact ih hrest'

/-! ## A call trace is a forward on `AState` -/

lemma engineV35_project_cons (c : VCall) (cs : List VCall) :
    VCall.project (c :: cs) = c.toCall.toList ++ VCall.project cs := by
  unfold VCall.project
  rw [List.filterMap_cons]
  cases c.toCall <;> rfl

/-- One call of a trace is one call of `Forward`, or leaves `AState` alone. -/
lemma engineV35_vopStep_project {K : Config} {ctx : Option LegDomain} {a : Address}
    {s s' : VState} {op : VOp} (h : VOpStep K ctx a s op s') :
    FRun K s.a (VCall.mk a op).toCall.toList s'.a := by
  cases h with
  | fwd ho _ => exact FRun.cons ho FRun.nil
  | ctmCodeSwap hpa _ => exact FRun.cons (OpStep.ctmCodeSwap hpa) FRun.nil
  | ctmSetPendingAdmin _ => exact FRun.nil
  | ctmAcceptAdmin _ => exact FRun.nil
  | ctmSetServerNotifier _ => exact FRun.nil
  | execTransferOwnership _ => rw [engineV35_setExec_a]; exact FRun.nil
  | execAcceptOwnership _ => rw [engineV35_setExec_a]; exact FRun.nil
  | execSlots _ _ => rw [engineV35_setExec_a]; exact FRun.nil
  | ecoTransferOwnership _ _ => exact FRun.nil
  | ecoRenounceOwnership _ => exact FRun.nil
  | notifierTransferOwnership _ => exact FRun.nil
  | notifierAcceptOwnership _ => exact FRun.nil
  | notifierRenounceOwnership _ => exact FRun.nil
  | notifierSetChainTypeManager _ _ => exact FRun.nil
  | notifierChangeAdmin _ _ => exact FRun.nil
  | notifierCodeSwap _ => exact FRun.nil

lemma engineV35_vrun_frun {K : Config} {ctx : Option LegDomain} {s s' : VState}
    {cs : List VCall} (h : VRun K ctx s cs s') : FRun K s.a (VCall.project cs) s'.a := by
  induction h with
  | nil => exact FRun.nil
  | @cons s₁ s₂ s₃ c cs hstep _ ih =>
      rw [engineV35_project_cons]
      exact frun_append (engineV35_vopStep_project hstep) ih

lemma engineV35_project_mem {cs : List VCall} {c : Call} (h : c ∈ VCall.project cs) :
    ∃ c' ∈ cs, c'.toCall = some c := by
  unfold VCall.project at h
  exact List.mem_filterMap.mp h

/-- A projected call hands authority to the migration, or replaces the CTM's code, only if
the call it comes from does. -/
lemma engineV35_toCall_props {K : Config} {c' : VCall} {c : Call} (h : c'.toCall = some c) :
    (c.op.handsToMigration K → c'.op.handsToMigration K) ∧
      (c.op.swapsCtmCode → c'.op.swapsCtmCode) := by
  obtain ⟨a, op⟩ := c'
  cases op with
  | fwd op =>
      have hc : c = ⟨a, op⟩ := (Option.some.inj h).symm
      subst hc
      exact ⟨id, id⟩
  | ctmCodeSwap o p v r adm padm nf ans =>
      have hc : c = ⟨a, .ctmCodeSwap o p v r⟩ := (Option.some.inj h).symm
      subst hc
      exact ⟨fun h' => h'.elim, fun _ => trivial⟩
  | ctmSetPendingAdmin x => exact nomatch h
  | ctmAcceptAdmin => exact nomatch h
  | ctmSetServerNotifier x => exact nomatch h
  | execTransferOwnership d x => exact nomatch h
  | execAcceptOwnership d => exact nomatch h
  | execRenounceOwnership d => exact nomatch h
  | execSlots d o p => exact nomatch h
  | ecoTransferOwnership x => exact nomatch h
  | ecoRenounceOwnership => exact nomatch h
  | notifierTransferOwnership n x => exact nomatch h
  | notifierAcceptOwnership n => exact nomatch h
  | notifierRenounceOwnership n => exact nomatch h
  | notifierSetChainTypeManager n x => exact nomatch h
  | notifierChangeAdmin n x => exact nomatch h
  | notifierCodeSwap n o p c adm => exact nomatch h

/-! ## What a trace keeps -/

/-- A call from a spent state leaves it spent. -/
lemma engineV35_opStep_spent {K : Config} {a : Address} {s s' : AState} {op : Op}
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

lemma engineV35_frun_spent {K : Config} {s s' : AState} {cs : List Call} (h : FRun K s cs s') :
    s.executed = true → s'.executed = true := by
  induction h with
  | nil => exact id
  | cons hstep _ ih => exact fun hx => ih (engineV35_opStep_spent hx hstep)

/-- The CTM keeps answering its ownership reads from its slots unless a call swaps in code
that answers them falsely. -/
lemma engineV35_vopStep_answers {K : Config} {ctx : Option LegDomain} {a : Address}
    {s s' : VState} {op : VOp} (h : VOpStep K ctx a s op s') (hc : ¬ op.answersFalsely)
    (ha : s.ctmAnswers = none) : s'.ctmAnswers = none := by
  cases h with
  | fwd _ _ => exact ha
  | @ctmCodeSwap o p v r adm padm nf ans _ _ =>
      cases ans with
      | none => rfl
      | some x => exact absurd trivial hc
  | ctmSetPendingAdmin _ => exact ha
  | ctmAcceptAdmin _ => exact ha
  | ctmSetServerNotifier _ => exact ha
  | execTransferOwnership _ => rw [engineV35_setExec_ctmAnswers]; exact ha
  | execAcceptOwnership _ => rw [engineV35_setExec_ctmAnswers]; exact ha
  | execSlots _ _ => rw [engineV35_setExec_ctmAnswers]; exact ha
  | ecoTransferOwnership _ _ => exact ha
  | ecoRenounceOwnership _ => exact ha
  | notifierTransferOwnership _ => exact ha
  | notifierAcceptOwnership _ => exact ha
  | notifierRenounceOwnership _ => exact ha
  | notifierSetChainTypeManager _ _ => exact ha
  | notifierChangeAdmin _ _ => exact ha
  | notifierCodeSwap _ => exact ha

lemma engineV35_vrun_answers {K : Config} {ctx : Option LegDomain} {s s' : VState}
    {cs : List VCall} (h : VRun K ctx s cs s') :
    (∀ c ∈ cs, ¬ c.op.answersFalsely) → s.ctmAnswers = none → s'.ctmAnswers = none := by
  induction h with
  | nil => exact fun _ ha => ha
  | cons hstep _ ih =>
      exact fun hc ha => ih (fun c h' => hc c (List.mem_cons_of_mem _ h'))
        (engineV35_vopStep_answers hstep (hc _ List.mem_cons_self) ha)

lemma engineV35_answersFalsely_swaps {op : VOp} (h : op.answersFalsely) : op.swapsCtmCode := by
  cases op with
  | ctmCodeSwap o p v r adm padm nf ans => trivial
  | fwd op => exact h.elim
  | ctmSetPendingAdmin x => exact h.elim
  | ctmAcceptAdmin => exact h.elim
  | ctmSetServerNotifier x => exact h.elim
  | execTransferOwnership d x => exact h.elim
  | execAcceptOwnership d => exact h.elim
  | execRenounceOwnership d => exact h.elim
  | execSlots d o p => exact h.elim
  | ecoTransferOwnership x => exact h.elim
  | ecoRenounceOwnership => exact h.elim
  | notifierTransferOwnership n x => exact h.elim
  | notifierAcceptOwnership n => exact h.elim
  | notifierRenounceOwnership n => exact h.elim
  | notifierSetChainTypeManager n x => exact h.elim
  | notifierChangeAdmin n x => exact h.elim
  | notifierCodeSwap n o p c adm => exact h.elim

/-- A trace with no ownership call naming the migration and no CTM code swap, from a spent
state with nothing parked: `Forward`'s `frun_keeps_unparked` on the projected calls. -/
lemma engineV35_vrun_keeps_unparked {K : Config} {ctx : Option LegDomain} {s s' : VState}
    {cs : List VCall} (h : VRun K ctx s cs s')
    (hc : ∀ c ∈ cs, ¬ c.op.handsToMigration K ∧ ¬ c.op.swapsCtmCode)
    (hx : s.a.executed = true) (hp : ¬ ParkedOnMigration K s.a) (ha : s.ctmAnswers = none) :
    s'.a.executed = true ∧ ¬ ParkedOnMigration K s'.a ∧ s'.ctmAnswers = none := by
  have hproj : ∀ c ∈ VCall.project cs, ¬ c.op.handsToMigration K ∧ ¬ c.op.swapsCtmCode := by
    intro c hmem
    obtain ⟨c', hc', hto⟩ := engineV35_project_mem hmem
    obtain ⟨h1, h2⟩ := engineV35_toCall_props (K := K) hto
    exact ⟨fun h' => (hc c' hc').1 (h1 h'), fun h' => (hc c' hc').2 (h2 h')⟩
  obtain ⟨hx', hp'⟩ := frun_keeps_unparked (engineV35_vrun_frun h) hx hp
    (fun c hm => (hproj c hm).1) (fun c hm => (hproj c hm).2)
  exact ⟨hx', hp',
    engineV35_vrun_answers h (fun c hm h' => (hc c hm).2 (engineV35_answersFalsely_swaps h')) ha⟩

/-! ## The frame for the domain a leg does not check -/

/-- One call of a CTM leg, sent by none of the core domain's holders. -/
lemma engineV35_vopStep_core_frame {K : Config} {a : Address} {s s' : VState} {op : VOp}
    (h : VOpStep K (some .ctm) a s op s') (h1 : a ≠ s.ecoOwner) (h2 : a ≠ s.cOwner)
    (h3 : a ≠ s.cPending) :
    s'.ecoOwner = s.ecoOwner ∧ s'.cOwner = s.cOwner ∧ s'.cPending = s.cPending := by
  cases h with
  | fwd _ _ => exact ⟨rfl, rfl, rfl⟩
  | ctmCodeSwap _ _ => exact ⟨rfl, rfl, rfl⟩
  | ctmSetPendingAdmin _ => exact ⟨rfl, rfl, rfl⟩
  | ctmAcceptAdmin _ => exact ⟨rfl, rfl, rfl⟩
  | ctmSetServerNotifier _ => exact ⟨rfl, rfl, rfl⟩
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
  | notifierSetChainTypeManager _ _ => exact ⟨rfl, rfl, rfl⟩
  | notifierChangeAdmin _ _ => exact ⟨rfl, rfl, rfl⟩
  | notifierCodeSwap _ => exact ⟨rfl, rfl, rfl⟩

lemma engineV35_vrun_core_frame {K : Config} {s s' : VState} {cs : List VCall}
    (h : VRun K (some .ctm) s cs s') :
    (∀ c ∈ cs, c.sender ≠ s.ecoOwner ∧ c.sender ≠ s.cOwner ∧ c.sender ≠ s.cPending) →
    s'.ecoOwner = s.ecoOwner ∧ s'.cOwner = s.cOwner ∧ s'.cPending = s.cPending := by
  induction h with
  | nil => exact fun _ => ⟨rfl, rfl, rfl⟩
  | @cons s₁ s₂ s₃ c cs hstep _ ih =>
      intro hq
      obtain ⟨q1, q2, q3⟩ := hq c List.mem_cons_self
      obtain ⟨e1, e2, e3⟩ := engineV35_vopStep_core_frame hstep q1 q2 q3
      obtain ⟨f1, f2, f3⟩ := ih (fun c' hc' => by
        rw [e1, e2, e3]; exact hq c' (List.mem_cons_of_mem _ hc'))
      exact ⟨f1.trans e1, f2.trans e2, f3.trans e3⟩

/-- One of `Forward`'s calls, sent by none of the CTM domain's holders and not `migrate()`. -/
lemma engineV35_opStep_quiet {K : Config} {a : Address} {s s' : AState} {op : Op}
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
lemma engineV35_vopStep_ctm_frame {K : Config} {a : Address} {s s' : VState} {op : VOp}
    (h : VOpStep K (some .core) a s op s') (h1 : a ≠ s.a.ctmOwner) (h2 : a ≠ s.a.ctmPending)
    (h3 : a ≠ s.a.paOwner) (h4 : a ≠ s.eOwner) (h5 : a ≠ s.ePending)
    (h6 : op ≠ .fwd .migrate) :
    s'.a.ctmOwner = s.a.ctmOwner ∧ s'.a.ctmPending = s.a.ctmPending ∧
      s'.a.paOwner = s.a.paOwner ∧ s'.eOwner = s.eOwner ∧ s'.ePending = s.ePending ∧
      s'.a.executed = s.a.executed := by
  cases h with
  | fwd ho _ =>
      obtain ⟨e1, e2, e3, e4⟩ := engineV35_opStep_quiet ho h1 h2 h3 (fun e => h6 (by rw [e]))
      exact ⟨e1, e2, e3, rfl, rfl, e4⟩
  | ctmCodeSwap hpa _ => exact absurd hpa.symm h3
  | ctmSetPendingAdmin _ => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | ctmAcceptAdmin _ => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | ctmSetServerNotifier _ => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
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
  | notifierSetChainTypeManager _ _ => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | notifierChangeAdmin _ _ => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | notifierCodeSwap _ => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma engineV35_vrun_ctm_frame {K : Config} {s s' : VState} {cs : List VCall}
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
      obtain ⟨e1, e2, e3, e4, e5, e6⟩ := engineV35_vopStep_ctm_frame hstep q1 q2 q3 q4 q5 q6
      obtain ⟨f1, f2, f3, f4, f5, f6⟩ := ih (fun c' hc' => by
        rw [e1, e2, e3, e4, e5]; exact hq c' (List.mem_cons_of_mem _ hc'))
      exact ⟨f1.trans e1, f2.trans e2, f3.trans e3, f4.trans e4, f5.trans e5, f6.trans e6⟩

/-! ## What equal holders say -/

/-- Equal CTM-domain holders are equal reads, entry by entry. -/
lemma engineV35_holders_ctm_inj {K : Config} {s s' : VState}
    (h : s'.holders K .ctm = s.holders K .ctm) :
    s'.a.paOwner = s.a.paOwner ∧ s'.ctmRead = s.ctmRead ∧ s'.ctmAdmin = s.ctmAdmin ∧
      s'.notifier = s.notifier ∧
      (s.notifier ≠ 0 →
        (s'.notifiers s.notifier).owner = (s.notifiers s.notifier).owner ∧
        (s'.notifiers s.notifier).pending = (s.notifiers s.notifier).pending ∧
        (s'.notifierAdminRead K s.notifier).getD 0 = (s.notifierAdminRead K s.notifier).getD 0 ∧
        (s'.notifiers s.notifier).ctm = (s.notifiers s.notifier).ctm) := by
  simp only [VState.holders, DomainHolders.ctm.injEq] at h
  obtain ⟨h1, h2, h3, h4, _, h6, h7⟩ := h
  refine ⟨h1, Prod.ext h2 h3, h4, h6, fun hn => ?_⟩
  rw [h6] at h7
  simp only [hn, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h7
  exact h7

/-- Equal CTM-domain holders, read from a CTM that answers from its slots, are equal slots. -/
lemma engineV35_holders_ctm_eq {K : Config} {s s' : VState}
    (h : s'.holders K .ctm = s.holders K .ctm)
    (ha : s.ctmAnswers = none) (ha' : s'.ctmAnswers = none) :
    s'.a.paOwner = s.a.paOwner ∧ s'.a.ctmOwner = s.a.ctmOwner ∧
      s'.a.ctmPending = s.a.ctmPending := by
  obtain ⟨h1, h2, _⟩ := engineV35_holders_ctm_inj h
  simp only [VState.ctmRead, ha, ha', Option.getD_none, Prod.mk.injEq] at h2
  exact ⟨h1, h2.1, h2.2⟩

lemma engineV35_holders_core_eq {K : Config} {s s' : VState}
    (h : s'.holders K .core = s.holders K .core) : s'.ecoOwner = s.ecoOwner := by
  simpa [VState.holders] using h

/-- Two reads that both succeed and agree under `getD` are equal. -/
lemma engineV35_option_eq_of_getD {r r' : Option Address} (h : r.getD 0 = r'.getD 0)
    (hs : r.isSome = true) (hs' : r'.isSome = true) : r = r' := by
  cases r with
  | none => exact absurd hs (by simp)
  | some x =>
      cases r' with
      | none => exact absurd hs' (by simp)
      | some y => simp only [Option.getD_some] at h; rw [h]

lemma engineV35_leg_parts {K : Config} {H : DomainHolders → UInt256} {d : LegDomain}
    {s s' : VState} {cs : List VCall} (h : EngineLeg K H d s cs s') :
    (d = .ctm → s.ctmAdmin ≠ K.m.pa) ∧ HoldersReadable K d s ∧ VRun K (some d) s cs s' ∧
      s'.execOwner d = s.execOwner d ∧ s'.execPending d = s.execPending d ∧
      HoldersReadable K d s' ∧ H (s'.holders K d) = H (s.holders K d) := by
  cases h with
  | mk hpre hr hrun ho hp hr' hH => exact ⟨hpre, hr, hrun, ho, hp, hr', hH⟩

/-- A trace whose end state is known succeeds as a leg exactly when the hash agrees on the
logged pair, given the leg's other checks. -/
lemma engineV35_leg_iff {K : Config} {H : DomainHolders → UInt256} {d : LegDomain}
    {s t : VState} {cs : List VCall} (hpre : d = .ctm → s.ctmAdmin ≠ K.m.pa)
    (hr : HoldersReadable K d s) (hrun : VRun K (some d) s cs t)
    (ho : t.execOwner d = s.execOwner d) (hp : t.execPending d = s.execPending d)
    (hr' : HoldersReadable K d t) :
    (∃ s', EngineLeg K H d s cs s') ↔ H (s.holders K d) = H (t.holders K d) := by
  constructor
  · rintro ⟨s', hleg⟩
    obtain ⟨_, _, hrun', _, _, _, hH⟩ := engineV35_leg_parts hleg
    rw [engineV35_vrun_det hrun' hrun] at hH
    exact hH.symm
  · intro hH
    exact ⟨t, EngineLeg.mk hpre hr hrun ho hp hr' hH.symm⟩

/-- The leg's own domain: equal holders, or a collision on the logged pair. -/
lemma engineV35_leg_own_frame {K : Config} {H : DomainHolders → UInt256} {d : LegDomain}
    {s s' : VState} {cs : List VCall} (h : EngineLeg K H d s cs s')
    (hans : d = .ctm → s.ctmAnswers = none ∧ s'.ctmAnswers = none) :
    (LegOwnFrame d s s' ∧ s'.holders K d = s.holders K d) ∨
      HoldersCollide H (s.holders K d) (s'.holders K d) := by
  obtain ⟨_, _, _, ho, hp, _, hH⟩ := engineV35_leg_parts h
  by_cases heq : s'.holders K d = s.holders K d
  · left
    refine ⟨?_, heq⟩
    cases d with
    | ctm =>
        obtain ⟨ha, ha'⟩ := hans rfl
        obtain ⟨h1, h2, h3⟩ := engineV35_holders_ctm_eq heq ha ha'
        exact ⟨h2, h3, h1, ho, hp⟩
    | core => exact ⟨engineV35_holders_core_eq heq, ho, hp⟩
  · exact Or.inr ⟨fun e => heq e.symm, hH.symm⟩

lemma engineV35_leg_other_frame {K : Config} {H : DomainHolders → UInt256} {d : LegDomain}
    {s s' : VState} {cs : List VCall} (h : EngineLeg K H d s cs s')
    (hq : OtherDomainQuiet d s cs) : LegOtherFrame d s s' := by
  obtain ⟨_, _, hrun, _⟩ := engineV35_leg_parts h
  cases d with
  | ctm => exact engineV35_vrun_core_frame hrun hq
  | core => exact engineV35_vrun_ctm_frame hrun hq

/-! ## Certificates: a leg can neither park nor unpark -/

theorem EngineLegKeepsItsExecutor : Properties.EngineLegKeepsItsExecutor := by
  intro K H d s s' cs h
  obtain ⟨_, _, _, ho, hp, _⟩ := engineV35_leg_parts h
  exact ⟨ho, hp⟩

theorem EngineLegOtherDomainFrame : Properties.EngineLegOtherDomainFrame :=
  fun _ _ _ _ _ _ h hq => engineV35_leg_other_frame h hq

theorem EngineLegOwnDomainFrameOrCollision : Properties.EngineLegOwnDomainFrameOrCollision :=
  fun _ _ _ _ _ _ h hans => engineV35_leg_own_frame h hans

theorem EngineLegFrameOrCollision : Properties.EngineLegFrameOrCollision := by
  intro K H d s s' cs h hq hans
  rcases engineV35_leg_own_frame h hans with ⟨hown, heq⟩ | hcol
  · left
    refine ⟨?_, heq⟩
    have hother := engineV35_leg_other_frame h hq
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
      rcases engineV35_leg_own_frame h hans with ⟨⟨o1, o2, o3, _, _⟩, _⟩ | hcol
      · exact Or.inl (hiff o1 o2 o3)
      · exact Or.inr hcol
  | core =>
      obtain ⟨p1, p2, p3, _⟩ := engineV35_leg_other_frame h (hq rfl)
      exact Or.inl (hiff p1 p2 p3)

theorem EngineLegKeepsCtmBindingsOrCollision :
    Properties.EngineLegKeepsCtmBindingsOrCollision := by
  intro K H s s' cs h
  obtain ⟨_, hr, _, _, _, hr', hH⟩ := engineV35_leg_parts h
  by_cases heq : s'.holders K .ctm = s.holders K .ctm
  · left
    refine ⟨?_, heq⟩
    obtain ⟨_, _, h3, h4, h5⟩ := engineV35_holders_ctm_inj heq
    refine ⟨h3, h4, fun hn => ?_⟩
    obtain ⟨n1, n2, n3, n4⟩ := h5 hn
    have hs : (s.notifierAdminRead K s.notifier).isSome = true := hr hn
    have hs' : (s'.notifierAdminRead K s.notifier).isSome = true := by
      have := hr' (by rw [h4]; exact hn)
      rwa [h4] at this
    exact ⟨n1, n2, n4, engineV35_option_eq_of_getD n3 hs' hs⟩
  · exact Or.inr ⟨fun e => heq e.symm, hH.symm⟩

/-! ## Certificates: a leg's calls are a forward -/

theorem CallTracesAreForwards : Properties.CallTracesAreForwards :=
  fun _ _ _ _ _ h => ⟨engineV35_vrun_frun h, fun _ hc => engineV35_project_mem hc⟩

theorem EngineLegCallsAreAForward : Properties.EngineLegCallsAreAForward :=
  fun _ _ _ _ _ _ h => engineV35_vrun_frun (engineV35_leg_parts h).2.2.1

/-- One transaction from a spent state with nothing parked and a CTM that answers from its
slots keeps all three, or it is a leg whose hash collides on its logged pair. -/
lemma engineV35_vsysStep_keeps_unparked {K : Config} {H : DomainHolders → UInt256}
    {s s' : VState} {v : VLabel} (h : VSysStep K H s v s') (hv : v.Clean K)
    (hx : s.a.executed = true) (hp : ¬ ParkedOnMigration K s.a) (ha : s.ctmAnswers = none) :
    (s'.a.executed = true ∧ ¬ ParkedOnMigration K s'.a ∧ s'.ctmAnswers = none) ∨
      ∃ (d : LegDomain) (cs : List VCall), v = .engineLeg d cs ∧ EngineLeg K H d s cs s' ∧
        HoldersCollide H (s.holders K d) (s'.holders K d) := by
  cases h with
  | tx hstep =>
      obtain ⟨hx', hp'⟩ := astep_keeps_unparked hx hp hv hstep
      exact Or.inl ⟨hx', hp', ha⟩
  | call hrun => exact Or.inl (engineV35_vrun_keeps_unparked hrun hv hx hp ha)
  | @engineLeg _ d cs hleg =>
      cases d with
      | core =>
          exact Or.inl (engineV35_vrun_keeps_unparked (engineV35_leg_parts hleg).2.2.1 hv hx hp ha)
      | ctm =>
          have hrun := (engineV35_leg_parts hleg).2.2.1
          have ha' : s'.ctmAnswers = none := engineV35_vrun_answers hrun hv ha
          have hx' : s'.a.executed = true := engineV35_frun_spent (engineV35_vrun_frun hrun) hx
          rcases engineV35_leg_own_frame hleg (fun _ => ⟨ha, ha'⟩) with
            ⟨⟨o1, o2, o3, _, _⟩, _⟩ | hcol
          · refine Or.inl ⟨hx', ?_, ha'⟩
            unfold ParkedOnMigration at hp ⊢
            rw [o1, o2, o3]
            exact hp
          · exact Or.inr ⟨.ctm, cs, rfl, hleg, hcol⟩

lemma engineV35_vsysRun_keeps_unparked {K : Config} {H : DomainHolders → UInt256}
    {s s' : VState} {vs : List VLabel} (h : VSysRun K H s vs s') :
    s.a.executed = true → ¬ ParkedOnMigration K s.a → s.ctmAnswers = none →
    (∀ v ∈ vs, v.Clean K) → ¬ ParkedOnMigration K s'.a ∨ RunLegCollides K H s vs s' := by
  induction h with
  | nil => exact fun _ hp _ _ => Or.inl hp
  | @cons s₁ s₂ s₃ v vs hstep hrest ih =>
      intro hx hp ha hc
      rcases engineV35_vsysStep_keeps_unparked hstep (hc v List.mem_cons_self) hx hp ha with
        ⟨hx2, hp2, ha2⟩ | ⟨d, cs, hv, hl, hcol⟩
      · rcases ih hx2 hp2 ha2 (fun v' h' => hc v' (List.mem_cons_of_mem _ h')) with
          hfin | ⟨vs₁, vs₂, d, cs, t, t', hvs, hr1, hl, hr2, hcol⟩
        · exact Or.inl hfin
        · refine Or.inr ⟨v :: vs₁, vs₂, d, cs, t, t', ?_, VSysRun.cons hstep hr1, hl, hr2, hcol⟩
          rw [hvs]
          rfl
      · subst hv
        exact Or.inr ⟨[], vs, d, cs, s₁, s₂, rfl, VSysRun.nil, hl, hrest, hcol⟩

lemma engineV35_astep_det {K : Config} {s t₁ t₂ : AState} {l : Label} (h₁ : AStep K s l t₁)
    (h₂ : AStep K s l t₂) : t₁ = t₂ := by
  cases h₁ with
  | migrate hm =>
      cases h₂ with
      | migrate hm' => rw [migrate_eq hm, migrate_eq hm']
  | bundle _ _ hm _ =>
      cases h₂ with
      | bundle _ _ hm' _ => rw [migrate_eq hm, migrate_eq hm']
  | nominate _ => cases h₂; rfl
  | accept _ _ => cases h₂; rfl
  | transferPA _ _ => cases h₂; rfl
  | legacyMove _ => cases h₂; rfl

lemma engineV35_vsysStep_det {K : Config} {H : DomainHolders → UInt256} {s t₁ t₂ : VState}
    {v : VLabel} (h₁ : VSysStep K H s v t₁) (h₂ : VSysStep K H s v t₂) : t₁ = t₂ := by
  cases h₁ with
  | tx ha =>
      cases h₂ with
      | tx ha' => rw [engineV35_astep_det ha ha']
  | call hr =>
      cases h₂ with
      | call hr' => exact engineV35_vrun_det hr hr'
  | engineLeg hl =>
      cases h₂ with
      | engineLeg hl' =>
          exact engineV35_vrun_det (engineV35_leg_parts hl).2.2.1 (engineV35_leg_parts hl').2.2.1

theorem EngineRunsDeterministic : Properties.EngineRunsDeterministic := by
  intro K H s t₁ t₂ vs h₁ h₂
  induction h₁ generalizing t₂ with
  | nil => cases h₂; rfl
  | cons hstep _ ih =>
      cases h₂ with
      | cons hstep' hrest' =>
          rw [engineV35_vsysStep_det hstep hstep'] at ih
          exact ih _ hrest'

theorem NoReparkingAcrossEngineLegs : Properties.NoReparkingAcrossEngineLegs :=
  fun _ _ _ _ _ hx hp ha h hc => engineV35_vsysRun_keeps_unparked h hx hp ha hc

theorem MigrateLeavesNothingParkedWithEngineLegs :
    Properties.MigrateLeavesNothingParkedWithEngineLegs := by
  intro K H t s s' vs hgen hm ha h hc
  obtain ⟨_, _, _, hnp, _⟩ := MigrateLeavesNothingParked K t s.a hgen hm
  exact engineV35_vsysRun_keeps_unparked h (MigrateIsOneShot K t s.a hm).1 hnp ha hc

/-! ## Certificates: the engine inside its executor -/

theorem EngineReachesOnlyAcceptCTMOwnership :
    Properties.EngineReachesOnlyAcceptCTMOwnership := by
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
lemma engineV35_vopStep_execOwner_ne_zero {K : Config} {ctx : Option LegDomain} {a : Address}
    {s s' : VState} {op : VOp} (h : VOpStep K ctx a s op s') (ha : a ≠ 0) (d' : LegDomain)
    (hctx : ctx ≠ some d') (h0 : s.execOwner d' ≠ 0) : s'.execOwner d' ≠ 0 := by
  cases h with
  | fwd _ _ => exact h0
  | ctmCodeSwap _ _ => exact h0
  | ctmSetPendingAdmin _ => exact h0
  | ctmAcceptAdmin _ => exact h0
  | ctmSetServerNotifier _ => exact h0
  | @execTransferOwnership d x ho =>
      by_cases hd : d' = d
      · subst hd; rw [engineV35_setExec_execOwner]; exact h0
      · rw [engineV35_setExec_execOwner_ne _ hd]; exact h0
  | @execAcceptOwnership d hp =>
      by_cases hd : d' = d
      · subst hd; rw [engineV35_setExec_execOwner]; exact ha
      · rw [engineV35_setExec_execOwner_ne _ hd]; exact h0
  | @execSlots d o p hc _ =>
      by_cases hd : d' = d
      · subst hd; exact absurd hc hctx
      · rw [engineV35_setExec_execOwner_ne _ hd]; exact h0
  | ecoTransferOwnership _ _ => exact h0
  | ecoRenounceOwnership _ => exact h0
  | notifierTransferOwnership _ => exact h0
  | notifierAcceptOwnership _ => exact h0
  | notifierRenounceOwnership _ => exact h0
  | notifierSetChainTypeManager _ _ => exact h0
  | notifierChangeAdmin _ _ => exact h0
  | notifierCodeSwap _ => exact h0

lemma engineV35_vrun_execOwner_ne_zero {K : Config} {ctx : Option LegDomain} {s s' : VState}
    {cs : List VCall} (h : VRun K ctx s cs s') (d' : LegDomain) (hctx : ctx ≠ some d') :
    (∀ c ∈ cs, c.sender ≠ 0) → s.execOwner d' ≠ 0 → s'.execOwner d' ≠ 0 := by
  induction h with
  | nil => exact fun _ h0 => h0
  | cons hstep _ ih =>
      exact fun hs h0 => ih (fun c hc => hs c (List.mem_cons_of_mem _ hc))
        (engineV35_vopStep_execOwner_ne_zero hstep (hs _ List.mem_cons_self) d' hctx h0)

lemma engineV35_vsysStep_execOwner_ne_zero {K : Config} {H : DomainHolders → UInt256}
    {s s' : VState} {v : VLabel} (h : VSysStep K H s v s') (hs : v.SendersNonzero)
    (d' : LegDomain) (h0 : s.execOwner d' ≠ 0) : s'.execOwner d' ≠ 0 := by
  cases h with
  | tx _ => exact h0
  | call hrun => exact engineV35_vrun_execOwner_ne_zero hrun d' (fun h => nomatch h) hs h0
  | @engineLeg _ d cs hleg =>
      obtain ⟨_, _, hrun, ho, _⟩ := engineV35_leg_parts hleg
      by_cases hd : d' = d
      · subst hd; rw [ho]; exact h0
      · exact engineV35_vrun_execOwner_ne_zero hrun d' (fun h => hd (Option.some.inj h).symm) hs h0

lemma engineV35_vsysRun_execOwner_ne_zero {K : Config} {H : DomainHolders → UInt256}
    {s s' : VState} {vs : List VLabel} (h : VSysRun K H s vs s') (d' : LegDomain) :
    (∀ v ∈ vs, v.SendersNonzero) → s.execOwner d' ≠ 0 → s'.execOwner d' ≠ 0 := by
  induction h with
  | nil => exact fun _ h0 => h0
  | cons hstep _ ih =>
      exact fun hs h0 => ih (fun v hv => hs v (List.mem_cons_of_mem _ hv))
        (engineV35_vsysStep_execOwner_ne_zero hstep (hs _ List.mem_cons_self) d' h0)

lemma engineV35_no_execRenounce (K : Config) (ctx : Option LegDomain) (a : Address)
    (s t : VState) (d : LegDomain) : ¬ VOpStep K ctx a s (.execRenounceOwnership d) t :=
  fun h => nomatch h

theorem ExecutorOwnerNeverZero : Properties.ExecutorOwnerNeverZero := by
  refine ⟨?_, ?_, engineV35_no_execRenounce, ?_⟩
  · intro o own p h
    cases h with
    | mk ho => exact ho
  · intro own p h
    cases h with
    | mk ho => exact ho rfl
  · intro K H s s' vs h hs he hc
    exact ⟨engineV35_vsysRun_execOwner_ne_zero h .ctm hs he,
      engineV35_vsysRun_execOwner_ne_zero h .core hs hc⟩

/-! ## The witness states -/

/-- A CTM-domain state whose named notifier is administered by the `ProxyAdmin` passes the
reads. -/
lemma engineV35_readable_of {K : Config} {s : VState}
    (h : s.notifier ≠ 0 → (s.notifiers s.notifier).proxyAdmin = K.m.pa) :
    HoldersReadable K .ctm s := by
  intro hn
  simp [VState.notifierAdminRead, h hn]

private lemma engineV35_not_parked_postV : ¬ ParkedOnMigration (wConfig true) wPostV.a := by
  unfold ParkedOnMigration; decide

private lemma engineV35_auth : ExecutorAuthorities (wConfig true) :=
  ⟨⟨9, 0, 1, 2, true⟩, ⟨9, 0, 0, 0, true⟩, by simp [wConfig, wExec, wManifest],
    by simp [wConfig, wExec, wManifest], rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private lemma engineV35_migratePost : MigrateStep (wConfig true) wHanded wPost := by
  have hcomp : executorAccept (wConfig true) (handOn (wConfig true)
      (claim (wConfig true) wHanded)) = wPost := by decide
  exact hcomp ▸ MigrateStep.mk rfl (by decide) rfl engineV35_auth rfl rfl (by decide) (by decide)

/-! ## Certificates: the pre-check, (c), (d) and the bindings -/

theorem EngineLegRefusesCtmAdminProxyAdmin : Properties.EngineLegRefusesCtmAdminProxyAdmin := by
  have hrun : VRun (wConfig true) (some .ctm) wPostV wTransientLeg wPostV :=
    VRun.cons (VOpStep.fwd (OpStep.ctmTransferOwnership rfl) id)
      (VRun.cons (VOpStep.fwd (OpStep.ctmAcceptOwnership rfl) id)
        (VRun.cons (VOpStep.fwd (OpStep.ctmTransferOwnership rfl) id)
          (VRun.cons (VOpStep.fwd (OpStep.ctmAcceptOwnership rfl) id) VRun.nil)))
  refine ⟨?_, fun H => EngineLeg.mk (fun _ => by decide) (engineV35_readable_of fun _ => rfl)
    hrun rfl rfl (engineV35_readable_of fun _ => rfl) rfl, ?_⟩
  · intro K H s s' cs hadm hleg
    exact (engineV35_leg_parts hleg).1 rfl hadm
  · intro H s' hleg
    exact (engineV35_leg_parts hleg).1 rfl rfl

theorem LegCannotRecoverParkedCTM : Properties.LegCannotRecoverParkedCTM := by
  have hstep : ∀ ctx, VOpStep (wConfig false) ctx 3 wParkedV (.fwd .ctmAcceptOwnership)
      wRecoveredV := fun ctx => VOpStep.fwd (OpStep.ctmAcceptOwnership rfl) id
  refine ⟨?_, ⟨wRecoveredV, VRun.cons (hstep none) VRun.nil, rfl, rfl, ?_⟩, ?_, by decide⟩
  · intro H s s' cs hs ha ha' hleg
    rcases engineV35_leg_own_frame hleg (fun _ => ⟨ha, ha'⟩) with ⟨⟨o1, o2, _, _, _⟩, _⟩ | hcol
    · left
      have h1 : s'.a.ctmOwner = 50 := by rw [o1, hs]; rfl
      have h2 : s'.a.ctmPending = 3 := by rw [o2, hs]; rfl
      exact ⟨h1, h2, Or.inl h1⟩
    · exact Or.inr hcol
  · unfold ParkedOnMigration; decide
  · intro H
    exact engineV35_leg_iff (fun _ => by decide) (engineV35_readable_of fun _ => rfl)
      (VRun.cons (hstep _) VRun.nil) rfl rfl (engineV35_readable_of fun _ => rfl)

theorem LegRenounceReverts : Properties.LegRenounceReverts := by
  have hstep : ∀ ctx, VOpStep (wConfig true) ctx 3 wPostV (.fwd .ctmRenounceOwnership)
      wCtmRenouncedV := fun ctx => VOpStep.fwd (OpStep.ctmRenounceOwnership rfl) id
  refine ⟨?_, ?_, engineV35_no_execRenounce, ?_, by decide,
    ⟨wCtmRenouncedV, VRun.cons (hstep none) VRun.nil, rfl, rfl⟩⟩
  · intro K H s s' cs hleg ha ha' h1 h2
    by_cases heq : s'.holders K .ctm = s.holders K .ctm
    · left
      obtain ⟨e1, e2, e3⟩ := engineV35_holders_ctm_eq heq ha ha'
      obtain ⟨_, _, _, _, e5⟩ := engineV35_holders_ctm_inj heq
      exact ⟨by rw [e2]; exact h1, by rw [e1]; exact h2,
        fun hn h3 => by rw [(e5 hn).1]; exact h3⟩
    · exact Or.inr ⟨fun e => heq e.symm, (engineV35_leg_parts hleg).2.2.2.2.2.2.symm⟩
  · intro K H s s' cs hleg h1
    rcases engineV35_leg_own_frame hleg (fun h => nomatch h) with ⟨⟨o1, _, _⟩, _⟩ | hcol
    · exact Or.inl (by rw [o1]; exact h1)
    · exact Or.inr hcol
  · intro H
    exact engineV35_leg_iff (fun _ => by decide) (engineV35_readable_of fun _ => rfl)
      (VRun.cons (hstep _) VRun.nil) rfl rfl (engineV35_readable_of fun _ => rfl)

/-! ## Certificates: the countermodels -/

theorem CollisionDisjunctNeeded : Properties.CollisionDisjunctNeeded := by
  have hstep : VOpStep (wConfig true) (some .ctm) 3 wPostV (.fwd (.paTransferOwnership 7))
      wPaMovedV := VOpStep.fwd (OpStep.paTransferOwnership rfl (by decide)) id
  have hr : HoldersReadable (wConfig true) .ctm wPostV := engineV35_readable_of fun _ => rfl
  have hr' : HoldersReadable (wConfig true) .ctm wPaMovedV := engineV35_readable_of fun _ => rfl
  refine ⟨fun H => engineV35_leg_iff (fun _ => by decide) hr (VRun.cons hstep VRun.nil) rfl rfl hr',
    by decide, ?_, rfl, rfl,
    ⟨fun _ => 0, wPaMovedV,
      EngineLeg.mk (fun _ => by decide) hr (VRun.cons hstep VRun.nil) rfl rfl hr' rfl, rfl, ?_⟩⟩
  · intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    exact ⟨by decide, by decide, by decide⟩
  · rintro ⟨_, _, h3, _⟩
    exact absurd h3 (by decide)

theorem NoHolderCheckReparks : Properties.NoHolderCheckReparks := by
  have hstep : VOpStep (wConfig true) (some .ctm) 3 wPostV (.fwd (.ctmTransferOwnership 50))
      wNominatedV := VOpStep.fwd (OpStep.ctmTransferOwnership rfl) id
  refine ⟨rfl, engineV35_not_parked_postV,
    EngineLegNoHolderCheck.mk (VRun.cons hstep VRun.nil) rfl rfl, Or.inr (Or.inl rfl), ?_,
    by decide⟩
  intro H
  exact engineV35_leg_iff (fun _ => by decide) (engineV35_readable_of fun _ => rfl)
    (VRun.cons hstep VRun.nil) rfl rfl (engineV35_readable_of fun _ => rfl)

theorem NoReparkingCollisionDisjunctNeeded :
    Properties.NoReparkingCollisionDisjunctNeeded := by
  have hstep : VOpStep (wConfig true) (some .ctm) 3 wPostV (.fwd (.ctmTransferOwnership 50))
      wNominatedV := VOpStep.fwd (OpStep.ctmTransferOwnership rfl) id
  have hleg : EngineLeg (wConfig true) (fun _ => 0) .ctm wPostV
      [⟨3, .fwd (.ctmTransferOwnership 50)⟩] wNominatedV :=
    EngineLeg.mk (fun _ => by decide) (engineV35_readable_of fun _ => rfl)
      (VRun.cons hstep VRun.nil) rfl rfl (engineV35_readable_of fun _ => rfl) rfl
  refine ⟨rfl, engineV35_not_parked_postV, rfl,
    VSysRun.cons (VSysStep.engineLeg hleg) VSysRun.nil, ?_, Or.inr (Or.inl rfl),
    ⟨[], [], .ctm, [⟨3, .fwd (.ctmTransferOwnership 50)⟩], wPostV, wNominatedV, rfl,
      VSysRun.nil, hleg, VSysRun.nil, by decide, rfl⟩⟩
  intro v hv
  rw [List.mem_singleton] at hv
  subst hv
  intro c hc
  rw [List.mem_singleton] at hc
  subst hc
  exact id

theorem EngineCtmSwapReparks : Properties.EngineCtmSwapReparks := by
  refine ⟨rfl, engineV35_not_parked_postV, ?_, ?_⟩
  · intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    exact id
  · intro H
    refine ⟨_, EngineLeg.mk (fun _ => by decide) (engineV35_readable_of fun _ => rfl)
      (VRun.cons (VOpStep.ctmCodeSwap rfl rfl) VRun.nil) rfl rfl
      (engineV35_readable_of fun _ => rfl) rfl, rfl, Or.inl rfl, fun h => nomatch h⟩

theorem CoreLegMayRunMigrate : Properties.CoreLegMayRunMigrate := by
  intro H
  have hstep : VOpStep (wConfig true) (some .core) 4 wHandedV (.fwd .migrate) wPostV :=
    VOpStep.fwd (OpStep.migrate engineV35_migratePost) id
  exact ⟨wPostV, EngineLeg.mk (fun h => nomatch h) trivial (VRun.cons hstep VRun.nil) rfl rfl
    trivial rfl, by decide, by decide, engineV35_not_parked_postV⟩

theorem OtherDomainQuietNeeded : Properties.OtherDomainQuietNeeded := by
  refine ⟨?_, ?_⟩
  · intro h
    exact (h _ List.mem_cons_self).1 rfl
  · intro H
    refine ⟨_, EngineLeg.mk (fun _ => by decide) (engineV35_readable_of fun _ => rfl)
      (VRun.cons (VOpStep.ecoTransferOwnership rfl (by decide)) VRun.nil) rfl rfl
      (engineV35_readable_of fun _ => rfl) rfl, rfl, rfl, ?_⟩
    rintro ⟨_, _, _, h4, _⟩
    exact absurd h4 (by decide)

theorem UnnamedNotifierIsUnchecked : Properties.UnnamedNotifierIsUnchecked := by
  refine ⟨?_, ?_, by decide⟩
  · intro H
    exact ⟨_, EngineLeg.mk (fun _ => by decide) (fun h => absurd rfl h)
      (VRun.cons (VOpStep.notifierRenounceOwnership rfl) VRun.nil) rfl rfl
      (fun h => absurd rfl h) rfl, rfl, by decide, by decide⟩
  · intro H
    exact engineV35_leg_iff (fun _ => by decide) (engineV35_readable_of fun _ => rfl)
      (VRun.cons (VOpStep.notifierRenounceOwnership rfl) VRun.nil) rfl rfl
      (engineV35_readable_of fun _ => by decide)

theorem CtmBindingsCollisionNeeded : Properties.CtmBindingsCollisionNeeded := by
  have hr : HoldersReadable (wConfig true) .ctm wPostV := engineV35_readable_of fun _ => rfl
  have hstep₂ : VOpStep (wConfig true) (some .ctm) 3 wPostV (.notifierSetChainTypeManager 8 5)
      wNotifierRepointedV := VOpStep.notifierSetChainTypeManager rfl (by decide)
  have hr₂ : HoldersReadable (wConfig true) .ctm wNotifierRepointedV :=
    engineV35_readable_of fun _ => by decide
  refine ⟨fun H => engineV35_leg_iff (fun _ => by decide) hr
      (VRun.cons (VOpStep.ctmSetServerNotifier rfl) VRun.nil) rfl rfl (fun h => absurd rfl h),
    by decide,
    fun H => engineV35_leg_iff (fun _ => by decide) hr (VRun.cons hstep₂ VRun.nil) rfl rfl hr₂,
    by decide,
    ⟨fun _ => 0, wNotifierRepointedV,
      EngineLeg.mk (fun _ => by decide) hr (VRun.cons hstep₂ VRun.nil) rfl rfl hr₂ rfl,
      by decide, ?_⟩⟩
  rintro ⟨_, _, hn⟩
  exact absurd (hn (by decide)).2.2.1 (by decide)

theorem EngineCtmAdminNominationUnseen : Properties.EngineCtmAdminNominationUnseen := by
  have hr : HoldersReadable (wConfig true) .ctm wPostV := engineV35_readable_of fun _ => rfl
  have h1 : VOpStep (wConfig true) (some .ctm) 3 wPostV (.ctmSetPendingAdmin 7)
      wAdminNominatedV := VOpStep.ctmSetPendingAdmin (Or.inr rfl)
  have h2 : ∀ ctx, VOpStep (wConfig true) ctx 7 wAdminNominatedV .ctmAcceptAdmin wAdminTakenV :=
    fun _ => VOpStep.ctmAcceptAdmin rfl
  refine ⟨fun H => EngineLeg.mk (fun _ => by decide) hr (VRun.cons h1 VRun.nil) rfl rfl
      (engineV35_readable_of fun _ => rfl) rfl, rfl, rfl, VRun.cons (h2 none) VRun.nil, rfl, rfl,
    fun H => engineV35_leg_iff (fun _ => by decide) hr (VRun.cons h1 (VRun.cons (h2 _) VRun.nil))
      rfl rfl (engineV35_readable_of fun _ => rfl),
    by decide⟩

theorem EngineGatePremisesNeeded : Properties.EngineGatePremisesNeeded := by
  refine ⟨fun K d s chainAdmin h => h.symm, fun K s chainAdmin id h => Or.inr h.symm, ?_⟩
  intro H
  have h1 : VOpStep (wConfig true) (some .ctm) 3 wPostV (.execSlots .ctm 3 0)
      (wPostV.setExec .ctm 3 0) := VOpStep.execSlots rfl rfl
  have h2 : VOpStep (wConfig true) (some .ctm) 3 (wPostV.setExec .ctm 3 0) (.execSlots .ctm 9 0)
      wPostV := VOpStep.execSlots rfl rfl
  exact ⟨EngineLeg.mk (fun _ => by decide) (engineV35_readable_of fun _ => rfl)
      (VRun.cons h1 (VRun.cons h2 VRun.nil)) rfl rfl (engineV35_readable_of fun _ => rfl) rfl,
    VRun.cons h1 VRun.nil⟩

/-! ## Certificates: the witnesses -/

private lemma engineV35_transient_run :
    VRun (wConfig true) (some .ctm) wPostV wTransientLeg wPostV :=
  VRun.cons (VOpStep.fwd (OpStep.ctmTransferOwnership rfl) id)
    (VRun.cons (VOpStep.fwd (OpStep.ctmAcceptOwnership rfl) id)
      (VRun.cons (VOpStep.fwd (OpStep.ctmTransferOwnership rfl) id)
        (VRun.cons (VOpStep.fwd (OpStep.ctmAcceptOwnership rfl) id) VRun.nil)))

private lemma engineV35_eco_run :
    VRun (wConfig true) (some .core) wPostV wEcoRoundTrip wPostV :=
  VRun.cons (VOpStep.ecoTransferOwnership rfl (by decide))
    (VRun.cons (VOpStep.ecoTransferOwnership rfl (by decide)) VRun.nil)

theorem EngineLegTransientWitness : Properties.EngineLegTransientWitness := by
  have hleg : ∀ H : DomainHolders → UInt256,
      EngineLeg (wConfig true) H .ctm wPostV wTransientLeg wPostV :=
    fun H => EngineLeg.mk (fun _ => by decide) (engineV35_readable_of fun _ => rfl)
      engineV35_transient_run rfl rfl (engineV35_readable_of fun _ => rfl) rfl
  have hcore : ∀ H : DomainHolders → UInt256,
      EngineLeg (wConfig true) H .core wPostV wEcoRoundTrip wPostV :=
    fun H => EngineLeg.mk (fun h => nomatch h) trivial engineV35_eco_run rfl rfl trivial rfl
  have hquiet : OtherDomainQuiet .ctm wPostV wTransientLeg := by
    intro c hc
    simp only [wTransientLeg, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩
  refine ⟨hleg, ⟨_, VRun.cons (VOpStep.fwd (OpStep.ctmTransferOwnership rfl) id)
      (VRun.cons (VOpStep.fwd (OpStep.ctmAcceptOwnership rfl) id) VRun.nil), rfl⟩,
    hquiet, rfl, rfl, engineV35_not_parked_postV, by decide, by decide, ?_⟩
  intro H
  refine ⟨VSysRun.cons (VSysStep.engineLeg (hleg H))
    (VSysRun.cons (VSysStep.engineLeg (hcore H)) VSysRun.nil), ?_, ?_⟩
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · refine ⟨?_, ?_⟩
      · intro c hc
        simp only [wTransientLeg, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> exact id
      · intro c hc
        simp only [wTransientLeg, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> decide
    · refine ⟨?_, ?_⟩
      · intro c hc
        simp only [wEcoRoundTrip, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> exact ⟨id, id⟩
      · intro c hc
        simp only [wEcoRoundTrip, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> decide
  · intro c hc
    simp only [wEcoRoundTrip, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
      exact ⟨by decide, by decide, by decide, by decide, by decide, fun h => nomatch h⟩

theorem EngineLegPremisesWitness : Properties.EngineLegPremisesWitness := by
  have hpa₁ : VOpStep (wConfig false) (some .ctm) 3 wParkedV (.fwd (.paTransferOwnership 7))
      { wParkedV with a := { wParked with paOwner := 7 } } :=
    VOpStep.fwd (OpStep.paTransferOwnership rfl (by decide)) id
  have hpa₂ : VOpStep (wConfig false) (some .ctm) 7
      { wParkedV with a := { wParked with paOwner := 7 } } (.fwd (.paTransferOwnership 3))
      wParkedV := VOpStep.fwd (OpStep.paTransferOwnership rfl (by decide)) id
  have hnf₁ : VOpStep (wConfig true) (some .ctm) 3 wPostV (.ctmSetServerNotifier 0)
      wNoNotifierV := VOpStep.ctmSetServerNotifier rfl
  have hnf₂ : VOpStep (wConfig true) (some .ctm) 3 wNoNotifierV (.ctmSetServerNotifier 8)
      wPostV := VOpStep.ctmSetServerNotifier rfl
  have hr : HoldersReadable (wConfig true) .ctm wPostV := engineV35_readable_of fun _ => rfl
  have hr₀ : HoldersReadable (wConfig false) .ctm wParkedV := engineV35_readable_of fun _ => rfl
  refine ⟨rfl, rfl,
    fun H => EngineLeg.mk (fun _ => by decide) hr₀ (VRun.cons hpa₁ (VRun.cons hpa₂ VRun.nil))
      rfl rfl hr₀ rfl,
    ⟨_, VRun.cons hpa₁ VRun.nil, rfl⟩,
    by decide, by decide, by decide, by decide,
    fun H => EngineLeg.mk (fun h => nomatch h) trivial engineV35_eco_run rfl rfl trivial rfl,
    ⟨_, VRun.cons (VOpStep.ecoTransferOwnership rfl (by decide)) VRun.nil, rfl⟩,
    by decide,
    fun H => EngineLeg.mk (fun _ => by decide) hr (VRun.cons hnf₁ (VRun.cons hnf₂ VRun.nil))
      rfl rfl hr rfl,
    ⟨_, VRun.cons hnf₁ VRun.nil, rfl⟩,
    ?_, engineV35_migratePost, trivial, by decide, by decide,
    fun _ => (by decide : (0 : Address) ≠ 3), Or.inr rfl, rfl,
    ExecConstructed.mk (by decide)⟩
  intro e he
  have hE : (wConfig true).exec (wConfig true).m.E = some ⟨9, 0, 1, 2, true⟩ := by
    simp [wConfig, wExec, wManifest]
  rw [hE] at he
  cases he
  rfl

end Contracts.RegistryBootstrapMigration
