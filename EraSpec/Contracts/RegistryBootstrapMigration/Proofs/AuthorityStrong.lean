import EraSpec.Contracts.RegistryBootstrapMigration.Properties.AuthorityStrong
import EraSpec.Contracts.RegistryBootstrapMigration.Proofs.Forward

/-!
# Proofs: who can move a CTM parked on the spent migration

The one-call frame is a case split over `OpStep`. Once the edge is spent, `migrate()` has no
step (`migrate_guards`). The owner-only CTM calls need the sender to be the migration, which
the premise excludes. The accept needs the sender to be the nominee. A code swap needs the
sender to own the `ProxyAdmin`.

The first-exit result is an induction over the calls: while a call leaves the owner and the
nominee alone the parked state persists, and the first call that changes them is classified by
the one-call frame. Custody is the same induction for the `ProxyAdmin`'s owner. The label
runs become call runs label by label, as in `LabelsAreCoveredCalls`, using only that the edge
is spent.

The countermodel and the witness are concrete runs.
-/

namespace Contracts.RegistryBootstrapMigration

/-! ## Calls from a spent state -/

/-- A call from a spent state keeps the edge spent: `migrate()` has no step there. -/
lemma authorityStrong_opStep_spent {K : Config} {a : Address} {s s' : AState} {op : Op}
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

/-- One call by someone other than the migration, while the spent migration owns the CTM. -/
lemma authorityStrong_parked_call {K : Config} {a : Address} {s s' : AState} {op : Op}
    (ho : s.ctmOwner = K.M) (hx : s.executed = true) (haM : a ≠ K.M)
    (h : OpStep K a s op s') :
    (s'.ctmOwner = K.M ∧ s'.ctmPending = s.ctmPending ∧ s'.executed = true) ∨
      (op = .ctmAcceptOwnership ∧ a = s.ctmPending ∧ s'.ctmOwner = s.ctmPending ∧
        s'.ctmPending = 0) ∨
      (op.swapsCtmCode ∧ a = s.paOwner) := by
  cases h with
  | ctmTransferOwnership ho' => exact absurd (ho'.symm.trans ho) haM
  | ctmAcceptOwnership hq => exact Or.inr (Or.inl ⟨rfl, hq.symm, hq.symm, rfl⟩)
  | ctmRenounceOwnership ho' => exact absurd (ho'.symm.trans ho) haM
  | ctmSetVersion ho' => exact absurd (ho'.symm.trans ho) haM
  | paTransferOwnership _ _ => exact Or.inl ⟨ho, rfl, hx⟩
  | paRenounceOwnership _ => exact Or.inl ⟨ho, rfl, hx⟩
  | ctmCodeSwap hpa => exact Or.inr (Or.inr ⟨trivial, hpa.symm⟩)
  | migrate hm =>
      have := (migrate_guards hm).1
      rw [hx] at this
      exact Bool.noConfusion this
  | untracked => exact Or.inl ⟨ho, rfl, hx⟩

/-- Along calls none sent by the migration, from a state where the spent migration owns the
CTM: the first call that changes the owner or the nominee is the start nominee's accept, or a
code swap by the `ProxyAdmin`'s owner of that moment. -/
lemma authorityStrong_first_exit {K : Config} {s s' : AState} {cs : List Call}
    (h : FRun K s cs s') : s.ctmOwner = K.M → s.executed = true →
    (∀ c ∈ cs, c.sender ≠ K.M) →
    (s'.ctmOwner = K.M ∧ s'.ctmPending = s.ctmPending) ∨
      ∃ (pre post : List Call) (c : Call) (t t' : AState), cs = pre ++ c :: post ∧
        FRun K s pre t ∧ OpStep K c.sender t c.op t' ∧ FRun K t' post s' ∧
        t.ctmOwner = K.M ∧ t.ctmPending = s.ctmPending ∧
        ¬ (t'.ctmOwner = K.M ∧ t'.ctmPending = s.ctmPending) ∧
        (c = ⟨s.ctmPending, .ctmAcceptOwnership⟩ ∨ (c.op.swapsCtmCode ∧ c.sender = t.paOwner)) := by
  induction h with
  | nil => intro ho _ _; exact Or.inl ⟨ho, rfl⟩
  | @cons s₁ s₂ s₃ c cs hstep hrest ih =>
      intro ho hx hs
      by_cases hu : s₂.ctmOwner = K.M ∧ s₂.ctmPending = s₁.ctmPending
      · -- the head call left the CTM parked with the same nominee: look further
        rcases ih hu.1 (authorityStrong_opStep_spent hx hstep)
            (fun c' hc' => hs c' (List.mem_cons_of_mem _ hc')) with
          ⟨h₁, h₂⟩ | ⟨pre, post, c', t, t', hcs, hpre, hc', hpost, ht₁, ht₂, hnt, hexit⟩
        · exact Or.inl ⟨h₁, h₂.trans hu.2⟩
        · refine Or.inr ⟨c :: pre, post, c', t, t', by rw [hcs, List.cons_append],
            FRun.cons hstep hpre, hc', hpost, ht₁, ht₂.trans hu.2, ?_, ?_⟩
          · rw [← hu.2]
            exact hnt
          · rw [← hu.2]
            exact hexit
      · -- the head call is the first exit
        refine Or.inr ⟨[], cs, c, s₁, s₂, rfl, FRun.nil, hstep, hrest, ho, rfl, hu, ?_⟩
        rcases authorityStrong_parked_call ho hx (hs c List.mem_cons_self) hstep with
          h₁ | ⟨hop, ha, _, _⟩ | ⟨hsw, ha⟩
        · exact absurd ⟨h₁.1, h₁.2.1⟩ hu
        · left
          obtain ⟨a, op⟩ := c
          simp only at hop ha
          rw [hop, ha]
        · exact Or.inr ⟨hsw, ha⟩

/-- One call from a spent state: the `ProxyAdmin`'s owner stays, becomes zero, or is the one
the call names. -/
lemma authorityStrong_opStep_custody {K : Config} {a : Address} {s s' : AState} {op : Op}
    (hx : s.executed = true) (h : OpStep K a s op s') :
    s'.paOwner = s.paOwner ∨ s'.paOwner = 0 ∨ op = .paTransferOwnership s'.paOwner := by
  cases h with
  | paTransferOwnership _ _ => exact Or.inr (Or.inr rfl)
  | paRenounceOwnership _ => exact Or.inr (Or.inl rfl)
  | migrate hm =>
      have := (migrate_guards hm).1
      rw [hx] at this
      exact Bool.noConfusion this
  | ctmTransferOwnership _ => exact Or.inl rfl
  | ctmAcceptOwnership _ => exact Or.inl rfl
  | ctmRenounceOwnership _ => exact Or.inl rfl
  | ctmSetVersion _ => exact Or.inl rfl
  | ctmCodeSwap _ => exact Or.inl rfl
  | untracked => exact Or.inl rfl

lemma authorityStrong_custody {K : Config} {s s' : AState} {cs : List Call}
    (h : FRun K s cs s') : s.executed = true →
    s'.paOwner = s.paOwner ∨ s'.paOwner = 0 ∨ ∃ c ∈ cs, c.op = .paTransferOwnership s'.paOwner := by
  induction h with
  | nil => intro _; exact Or.inl rfl
  | @cons s₁ s₂ s₃ c cs hstep _ ih =>
      intro hx
      rcases ih (authorityStrong_opStep_spent hx hstep) with h₁ | h₁ | ⟨c', hc', h₁⟩
      · rcases authorityStrong_opStep_custody hx hstep with h₂ | h₂ | h₂
        · exact Or.inl (h₁.trans h₂)
        · exact Or.inr (Or.inl (h₁.trans h₂))
        · exact Or.inr (Or.inr ⟨c, List.mem_cons_self, by rw [h₁]; exact h₂⟩)
      · exact Or.inr (Or.inl h₁)
      · exact Or.inr (Or.inr ⟨c', List.mem_cons_of_mem _ hc', h₁⟩)

/-- One label step from a spent state is one call, not sent by the migration, with that label. -/
lemma authorityStrong_astep_call {K : Config} {s s' : AState} {l : Label}
    (hx : s.executed = true) (h : AStep K s l s') :
    ∃ c : Call, c.sender ≠ K.M ∧ c.labels = [l] ∧ OpStep K c.sender s c.op s' := by
  cases h with
  | @nominate x hne =>
      exact ⟨⟨s.ctmOwner, .ctmTransferOwnership x⟩, hne, rfl, OpStep.ctmTransferOwnership rfl⟩
  | accept _ hpM =>
      exact ⟨⟨s.ctmPending, .ctmAcceptOwnership⟩, hpM, rfl, OpStep.ctmAcceptOwnership rfl⟩
  | @transferPA x hne hx0 =>
      exact ⟨⟨s.paOwner, .paTransferOwnership x⟩, hne, rfl, OpStep.paTransferOwnership rfl hx0⟩
  | @legacyMove v r hne =>
      exact ⟨⟨s.ctmOwner, .ctmSetVersion v r⟩, hne, rfl, OpStep.ctmSetVersion rfl⟩
  | migrate hm => exact absurd rfl (step_spent hx (AStep.migrate hm)).2.1
  | bundle a b hm c => exact absurd rfl (step_spent hx (AStep.bundle a b hm c)).2.2

end Contracts.RegistryBootstrapMigration

/-! ## Certificates -/

namespace Contracts.RegistryBootstrapMigration

theorem ParkedCTMLeavesByAcceptOrCodeSwap : Properties.ParkedCTMLeavesByAcceptOrCodeSwap := by
  intro K s s' c ho hx hcM h
  rcases authorityStrong_parked_call ho hx hcM h with h₁ | ⟨hop, ha, h₂, h₃⟩ | h₁
  · exact Or.inl h₁
  · refine Or.inr (Or.inl ⟨?_, h₂, h₃⟩)
    obtain ⟨a, op⟩ := c
    simp only at hop ha
    rw [hop, ha]
  · exact Or.inr (Or.inr h₁)

theorem ParkedCTMFirstExit : Properties.ParkedCTMFirstExit :=
  fun _ _ _ _ ho hx hs h => authorityStrong_first_exit h ho hx hs

theorem SpentProxyAdminCustody : Properties.SpentProxyAdminCustody :=
  fun _ _ _ _ hx h => authorityStrong_custody h hx

theorem SpentLabelRunsAreCalls : Properties.SpentLabelRunsAreCalls := by
  intro K s s' ls hx h
  induction h with
  | nil => exact ⟨[], fun _ hc => absurd hc List.not_mem_nil, rfl, FRun.nil⟩
  | @cons s₁ s₂ s₃ l ls hs _ ih =>
      obtain ⟨c, hcM, hcl, hc⟩ := authorityStrong_astep_call hx hs
      obtain ⟨cs, hcsM, hcsl, hcs⟩ := ih (step_spent hx hs).1
      refine ⟨c :: cs, fun c' hc' => ?_, ?_, FRun.cons hc hcs⟩
      · rcases List.mem_cons.mp hc' with rfl | hc''
        · exact hcM
        · exact hcsM c' hc''
      · rw [List.flatMap_cons, hcl, hcsl]
        rfl

end Contracts.RegistryBootstrapMigration

/-! ## The countermodel and the witness -/

namespace Contracts.RegistryBootstrapMigration

/-- Governance's hand-over, then the non-genuine executor's `migrate()`, which leaves `wParked`. -/
lemma authorityStrong_migrate_parks :
    MigrateStep (wConfig false) { wPre with ctmPending := 50, paOwner := 50 } wParked :=
  MigrateStep.mk (K := wConfig false) (s := { wPre with ctmPending := 50, paOwner := 50 })
    (by decide) (by decide) (by decide)
    ⟨⟨9, 0, 1, 2, false⟩, ⟨9, 0, 0, 0, true⟩, by decide, by decide, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl⟩
    (by decide) (by decide) (by decide) (by decide)

lemma authorityStrong_run_parks :
    ARun (wConfig false) wPre [.nominate 50, .transferPA 50, .migrate] wParked :=
  ARun.cons (AStep.nominate (by decide))
    (ARun.cons (AStep.transferPA (by decide) (by decide))
      (ARun.cons (AStep.migrate authorityStrong_migrate_parks) ARun.nil))

theorem ParkedPAOwnerNeedNotBeNominee : Properties.ParkedPAOwnerNeedNotBeNominee := by
  refine ⟨authorityStrong_run_parks, AStep.transferPA (by decide) (by decide), rfl, rfl,
    Or.inl rfl, by decide, by decide, FRun.cons (OpStep.ctmCodeSwap rfl) FRun.nil, rfl, ?_⟩
  rintro (⟨h, _⟩ | h)
  · exact absurd h (by decide)
  · rw [List.mem_singleton] at h
    exact absurd h (by decide)

theorem AuthorityStrongWitness : Properties.AuthorityStrongWitness := by
  have hhand : FRun (wConfig false) wParked [⟨3, .paTransferOwnership 7⟩] wParkedHandedOn :=
    FRun.cons (OpStep.paTransferOwnership rfl (by decide)) FRun.nil
  have hswap : OpStep (wConfig false) 7 wParkedHandedOn (.ctmCodeSwap 7 0 35 60) wParkedSwapped :=
    OpStep.ctmCodeSwap rfl
  refine ⟨rfl, rfl, FRun.cons (OpStep.ctmAcceptOwnership rfl) FRun.nil, ?_,
    FRun.cons (OpStep.paTransferOwnership rfl (by decide)) (FRun.cons hswap FRun.nil), rfl,
    hhand, rfl, rfl, hswap, by decide, rfl, by decide, by decide,
    ⟨_, List.mem_cons_self, rfl⟩,
    ARun.cons (AStep.transferPA (by decide) (by decide))
      (ARun.cons (AStep.accept (by decide) (by decide)) ARun.nil)⟩
  intro c hc
  simp only [wHandOnThenSwap, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> decide

end Contracts.RegistryBootstrapMigration
