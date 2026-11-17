import EraSpec.Contracts.ChainTypeManager.Properties.PendingL2UpgradeAtV35
import EraSpec.Contracts.ChainTypeManager.Proofs.UpgradeTimingStrong

/-!
# Proofs: the pending L2 upgrade transaction, at `draft/v0.35.0`

Every step of this model maps to at most one timed step between the same timed states
(`pstep_timed`), which gives the refinement and, through it, `ValidatedTimedRunsHaveNoDeadTime`
for runs of this model. The L2 gates then come from the two extra premises and `PendingInv`.

The negative results rest on one step lemma, `step_keeps`. From a `PendingUnbatched` state, a step
that is neither a break-glass cut nor an override at the chain's version keeps `PendingBlock` and
the deadline of the chain's version (`block_transfer` reads both off a handful of fields), and
leaves the upgrade batch unrecorded unless it is a commit of the chain at a block time at which
its version is active. Upgrades of the chain itself are refused by `PreviousUpgradeNotFinalized`
(`blocked`).

The witnesses are concrete runs over `pwWorld`, with every intermediate state written out.
-/

namespace Contracts.ChainTypeManager.PendingL2UpgradeAtV35

/-! ## Basic facts -/

private lemma minorOf_mono {a b : ℕ} (h : a ≤ b) : minorOf a ≤ minorOf b :=
  Nat.div_le_div_right h

private lemma not_patch_of_lt {a b : ℕ} (h : minorOf a < minorOf b) : ¬ PatchOnly a b :=
  fun hp => absurd hp (Nat.ne_of_lt h)

/-! ## The refinement -/

private lemma timedRun_append {T : TimedConfig} {s s' s'' : TimedSys} {l1 l2 : List TimedLabel}
    (h1 : TimedRun T s l1 s') (h2 : TimedRun T s' l2 s'') : TimedRun T s (l1 ++ l2) s'' := by
  induction h1 with
  | nil => exact h2
  | cons hs _ ih => exact TimedRun.cons hs (ih h2)

/-- A timed label that is not a routing step. -/
private lemma notBase_upgrade {id : ChainId} {path : UpgradePath} {caller : Address} {τ : ℕ} :
    ∀ l0, TimedLabel.upgrade id path caller τ ≠ .base l0 := fun _ h => by cases h

private lemma notBase_setAux {id : ChainId} {a : DiamondAux} :
    ∀ l0, TimedLabel.setAux id a ≠ .base l0 := fun _ h => by cases h

/-- One step of this model is a timed run of at most one step between the same timed states. Its
routing step, if any, is the step's own. -/
private lemma pstep_timed {C : PendingConfig} {s s' : PendingSys} {l : PLabel}
    (h : PStep C s l s') :
    ∃ ls' : List TimedLabel, TimedRun C.T s.ts ls' s'.ts ∧
      ∀ l' ∈ ls', (∀ l0, l' ≠ .base l0) ∨ ∃ l0, l' = .base l0 ∧ l = PLabel.base l0 := by
  cases h with
  | upgrade ht _ _ =>
      refine ⟨_, TimedRun.cons ht TimedRun.nil, fun l' hl' => ?_⟩
      rw [List.mem_singleton] at hl'
      subst hl'
      exact Or.inl notBase_upgrade
  | base ht _ _ =>
      refine ⟨_, TimedRun.cons ht TimedRun.nil, fun l' hl' => ?_⟩
      rw [List.mem_singleton] at hl'
      subst hl'
      exact Or.inr ⟨_, rfl, rfl⟩
  | setUpgradeTimestamp ht =>
      refine ⟨_, TimedRun.cons ht TimedRun.nil, fun l' hl' => ?_⟩
      rw [List.mem_singleton] at hl'
      subst hl'
      exact Or.inl (fun _ h => by cases h)
  | swapNotifier =>
      refine ⟨_, TimedRun.cons TimedStep.swapNotifier TimedRun.nil, fun l' hl' => ?_⟩
      rw [List.mem_singleton] at hl'
      subst hl'
      exact Or.inl (fun _ h => by cases h)
  | setRoles =>
      exact ⟨_, TimedRun.cons TimedStep.setAux TimedRun.nil, fun l' hl' => by
        rw [List.mem_singleton] at hl'; subst hl'; exact Or.inl notBase_setAux⟩
  | slMoves _ =>
      exact ⟨_, TimedRun.cons TimedStep.setAux TimedRun.nil, fun l' hl' => by
        rw [List.mem_singleton] at hl'; subst hl'; exact Or.inl notBase_setAux⟩
  | reinit _ _ _ =>
      exact ⟨_, TimedRun.cons TimedStep.setAux TimedRun.nil, fun l' hl' => by
        rw [List.mem_singleton] at hl'; subst hl'; exact Or.inl notBase_setAux⟩
  | commit _ _ _ =>
      exact ⟨_, TimedRun.cons TimedStep.setAux TimedRun.nil, fun l' hl' => by
        rw [List.mem_singleton] at hl'; subst hl'; exact Or.inl notBase_setAux⟩
  | prove _ _ => exact ⟨[], TimedRun.nil, fun _ h => absurd h List.not_mem_nil⟩
  | execute _ _ =>
      exact ⟨_, TimedRun.cons TimedStep.setAux TimedRun.nil, fun l' hl' => by
        rw [List.mem_singleton] at hl'; subst hl'; exact Or.inl notBase_setAux⟩
  | revertBatches _ _ _ =>
      exact ⟨_, TimedRun.cons TimedStep.setAux TimedRun.nil, fun l' hl' => by
        rw [List.mem_singleton] at hl'; subst hl'; exact Or.inl notBase_setAux⟩
  | setDeadline => exact ⟨[], TimedRun.nil, fun _ h => absurd h List.not_mem_nil⟩

theorem PendingRunIsATimedRun : Properties.PendingRunIsATimedRun := by
  intro C s s' ls h
  induction h with
  | nil => exact ⟨[], TimedRun.nil, fun _ h => absurd h List.not_mem_nil⟩
  | @cons s0 s1 s2 l ls hs _ ih =>
      obtain ⟨l1, h1, hc1⟩ := pstep_timed hs
      obtain ⟨l2, h2, hc2⟩ := ih
      refine ⟨l1 ++ l2, timedRun_append h1 h2, fun l' hl' => ?_⟩
      rcases List.mem_append.mp hl' with hm | hm
      · rcases hc1 l' hm with hnb | ⟨l0, rfl, hl⟩
        · exact Or.inl hnb
        · subst hl
          exact Or.inr ⟨l0, rfl, List.mem_cons_self⟩
      · rcases hc2 l' hm with hnb | ⟨l0, rfl, hl⟩
        · exact Or.inl hnb
        · exact Or.inr ⟨l0, rfl, List.mem_cons_of_mem _ hl⟩

/-- A premise on the labels of a run of this model gives one on the labels of the timed run
`PendingRunIsATimedRun` returns, when it holds of every timed label that is not a routing step
and passes from a routing label of this model to the same timed label. -/
private lemma timed_labels {ls : List PLabel} {ls' : List TimedLabel}
    (hcov : ∀ l' ∈ ls', (∀ l0, l' ≠ .base l0) ∨ ∃ l0, l' = .base l0 ∧ PLabel.base l0 ∈ ls)
    {P : TimedLabel → Prop} {Q : PLabel → Prop}
    (hnb : ∀ l', (∀ l0, l' ≠ .base l0) → P l') (hb : ∀ l0, Q (.base l0) → P (.base l0))
    (hq : ∀ l ∈ ls, Q l) : ∀ l' ∈ ls', P l' := by
  intro l' hl'
  rcases hcov l' hl' with hn | ⟨l0, rfl, hm⟩
  · exact hnb l' hn
  · exact hb l0 (hq _ hm)

/-! ## The invariant -/

private lemma pstep_inv {C : PendingConfig} {s s' : PendingSys} {l : PLabel}
    (hI : PendingInv s) (h : PStep C s l s') : PendingInv s' := by
  intro j hj
  cases h with
  | @upgrade id path caller τ ts' c ht hc hg =>
      by_cases hji : j = id
      · subst hji
        simp only [upd_same, l2After] at hj ⊢
        split_ifs at hj ⊢ with hcond
        · exfalso
          exact hj (hg.finalized hcond.1 (hg.patchNoTx hcond.1 hcond.2)).2
        · exact hI j hj
      · simp only [upd_ne _ _ hji] at hj ⊢
        exact hI j hj
  | base _ _ he =>
      cases he with
      | legacyCommit => exact hI j hj
      | bootstrapKeeps => exact hI j hj
      | @bootstrapSets id hh hb0 =>
          by_cases hji : j = id
          · subst hji
            simp only [upd_same] at hj
            exact absurd hb0 hj
          · simp only [upd_ne _ _ hji] at hj ⊢
            exact hI j hj
      | other _ _ => exact hI j hj
  | setUpgradeTimestamp _ => exact hI j hj
  | swapNotifier => exact hI j hj
  | setRoles => exact hI j hj
  | slMoves _ => exact hI j hj
  | @reinit id a x c _ _ hx =>
      by_cases hji : j = id
      · subst hji
        simp only [PendingSys.withBx, PendingSys.withAux, upd_same] at hj ⊢
        exact hx hj
      · simp only [PendingSys.withBx, PendingSys.withAux, upd_ne _ _ hji] at hj ⊢
        exact hI j hj
  | @commit id τ c _ _ _ =>
      by_cases hji : j = id
      · subst hji
        simp only [PendingSys.afterCommit, PendingSys.withBx, PendingSys.withAux, upd_same] at hj ⊢
        split_ifs at hj ⊢ with hcond
        · exact hcond.1
        · exact hI j hj
      · simp only [PendingSys.afterCommit, PendingSys.withBx, PendingSys.withAux,
          upd_ne _ _ hji] at hj ⊢
        exact hI j hj
  | @prove id k _ _ =>
      by_cases hji : j = id
      · subst hji
        simp only [PendingSys.withBx, upd_same] at hj ⊢
        exact hI j hj
      · simp only [PendingSys.withBx, upd_ne _ _ hji] at hj ⊢
        exact hI j hj
  | @execute id k _ _ =>
      by_cases hji : j = id
      · subst hji
        simp only [PendingSys.afterExecute, PendingSys.withBx, PendingSys.withAux,
          upd_same] at hj ⊢
        split_ifs at hj ⊢ with hcond
        · exact absurd rfl hj
        · exact hI j hj
      · simp only [PendingSys.afterExecute, PendingSys.withBx, PendingSys.withAux,
          upd_ne _ _ hji] at hj ⊢
        exact hI j hj
  | @revertBatches id n _ _ _ =>
      by_cases hji : j = id
      · subst hji
        simp only [PendingSys.afterRevert, PendingSys.withBx, PendingSys.withAux,
          upd_same] at hj ⊢
        split_ifs at hj with hn
        · exact absurd rfl hj
        · exact hI j hj
      · simp only [PendingSys.afterRevert, PendingSys.withBx, PendingSys.withAux,
          upd_ne _ _ hji] at hj ⊢
        exact hI j hj
  | setDeadline => exact hI j hj

theorem PendingInvAlongRuns : Properties.PendingInvAlongRuns := by
  intro C s s' ls hI h
  induction h with
  | nil => exact hI
  | cons hs _ ih => exact ih (pstep_inv hI hs)

/-! ## The block -/

/-- `PreviousUpgradeNotFinalized` / `PreviousUpgradeNotCleaned`, as one lemma. -/
private lemma blocked {C : PendingConfig} {s : PendingSys} {id : ChainId} {c : Chain}
    (hc : s.ts.sys.chains id = some c) (hsl : (s.ts.aux id).slVersion = none)
    (hmin : minorOf c.pv < minorOf (s.ts.sys.edge C.T.X.W c.pv).new)
    (hp : (s.bx id).txHash ≠ 0 ∨ (s.bx id).batch ≠ 0) {path : UpgradePath} {caller : Address}
    {τ : ℕ} : ¬ ∃ s', PStep C s (.upgrade id path caller τ) s' := by
  rintro ⟨s', h⟩
  cases h with
  | @upgrade _ _ _ _ _ c' _ hc' hg =>
      rw [hc] at hc'
      cases hc'
      obtain ⟨h0, h1⟩ := hg.finalized hsl (not_patch_of_lt hmin)
      rcases hp with hp | hp
      · exact hp h0
      · exact hp h1

theorem PendingTxBlocksEveryUpgrade : Properties.PendingTxBlocksEveryUpgrade := by
  intro C s id c hc hsl hmin hp path caller τ
  exact blocked hc hsl hmin hp

private lemma PendingBlock.blocks {C : PendingConfig} {s : PendingSys} {id : ChainId} {c : Chain}
    (hb : PendingBlock C s id c) {path : UpgradePath} {caller : Address} {τ : ℕ} :
    ¬ ∃ s', PStep C s (.upgrade id path caller τ) s' :=
  blocked hb.chain hb.onSL hb.minor (Or.inl hb.pending)

/-! ## One step from a `PendingUnbatched` state -/

/-- `PendingBlock` and the deadline of the chain's version carry over to a state that agrees on
the fields they read, with the CTM's version no lower and a committed edge at the chain's version
with the same deadline and a target no lower. -/
private lemma block_transfer {C : PendingConfig} {s s' : PendingSys} {id : ChainId} {c : Chain}
    (hb : PendingBlock C s id c)
    (hch : s'.ts.sys.chains id = s.ts.sys.chains id)
    (hpv : s.ts.sys.ctm.pv ≤ s'.ts.sys.ctm.pv)
    (hut : s'.ts.sys.ctm.ut c.pv ≠ 0)
    (hnew : (C.T.X.W.tr (s.ts.sys.ctm.ut c.pv)).new ≤ (C.T.X.W.tr (s'.ts.sys.ctm.ut c.pv)).new)
    (hdl : (C.T.sched (s'.ts.sys.ctm.ut c.pv)).deadline =
      (C.T.sched (s.ts.sys.ctm.ut c.pv)).deadline)
    (hleg : s'.ts.sys.ctm.legacy c.pv = s.ts.sys.ctm.legacy c.pv)
    (hd : s'.dl c.pv = s.dl c.pv)
    (hsl : (s'.ts.aux id).slVersion = (s.ts.aux id).slVersion)
    (htx : (s'.bx id).txHash = (s.bx id).txHash) :
    PendingBlock C s' id c ∧
      versionDeadline C.T s'.dl s'.ts.sys.ctm c.pv =
        versionDeadline C.T s.dl s.ts.sys.ctm c.pv := by
  refine ⟨⟨hch.trans hb.chain, lt_of_lt_of_le hb.behind hpv, hut,
    lt_of_lt_of_le hb.minor (minorOf_mono hnew), hleg.trans hb.noLegacy, htx ▸ hb.pending,
    hsl.trans hb.onSL⟩, ?_⟩
  simp [versionDeadline, hd, hut, hb.committed, hdl]

/-- `block_transfer` for a step that leaves the CTM alone. -/
private lemma block_frame {C : PendingConfig} {s s' : PendingSys} {id : ChainId} {c : Chain}
    (hb : PendingBlock C s id c) (hctm : s'.ts.sys.ctm = s.ts.sys.ctm)
    (hch : s'.ts.sys.chains id = s.ts.sys.chains id) (hd : s'.dl c.pv = s.dl c.pv)
    (hsl : (s'.ts.aux id).slVersion = (s.ts.aux id).slVersion)
    (htx : (s'.bx id).txHash = (s.bx id).txHash) :
    PendingBlock C s' id c ∧
      versionDeadline C.T s'.dl s'.ts.sys.ctm c.pv = versionDeadline C.T s.dl s.ts.sys.ctm c.pv :=
  block_transfer hb hch (by rw [hctm]) (by rw [hctm]; exact hb.committed) (by rw [hctm])
    (by rw [hctm]) (by rw [hctm]) hd hsl htx

/-- A routing transition moves one chain and leaves the CTM alone. -/
private lemma transition_frame {W : World} {s s' : Sys} {id : ChainId}
    (h : Step W s (.transition id) s') :
    s'.ctm = s.ctm ∧ ∀ j, j ≠ id → s'.chains j = s.chains j := by
  cases h with
  | transition _ _ _ _ _ => exact ⟨rfl, fun j hj => upd_ne _ _ hj⟩

/-- **The step lemma.** From a `PendingUnbatched` state, a step that is not a break-glass cut and
not an override at the chain's version keeps `PendingBlock` and the deadline of the chain's
version. The upgrade batch stays unrecorded, unless the step is a commit of the chain at a block
time at which the chain's version is active. -/
private lemma step_keeps {C : PendingConfig} {s s' : PendingSys} {l : PLabel} {id : ChainId}
    {c : Chain} (hw : PendingUnbatched C s id c) (h : PStep C s l s')
    (hna : ¬ l.isArbitrary) (hnd : ∀ t, l ≠ .setDeadline c.pv t) :
    (PendingBlock C s' id c ∧
      versionDeadline C.T s'.dl s'.ts.sys.ctm c.pv = versionDeadline C.T s.dl s.ts.sys.ctm c.pv) ∧
      ((s'.bx id).batch = 0 ∨
        ∃ τ', l = .commit id τ' ∧ ProtocolVersionActive C.T s.dl s.ts.sys.ctm c.pv τ') := by
  obtain ⟨hb, hb0⟩ := hw
  cases h with
  | @upgrade id' path caller τ' ts' c' ht hc' hg =>
      by_cases hid : id' = id
      · subst hid
        exact absurd ⟨_, PStep.upgrade ht hc' hg⟩ hb.blocks
      · obtain ⟨hstep, haux, -⟩ := UpgradeIsATransition C.T s.ts ts' id' path caller τ' ht
        obtain ⟨hctm, hchains⟩ := transition_frame hstep
        have hne : id ≠ id' := Ne.symm hid
        refine ⟨block_frame hb hctm (hchains id hne) rfl (by rw [haux]) ?_, Or.inl ?_⟩
        · show (upd s.bx id' (l2After C s id' c') id).txHash = (s.bx id).txHash
          rw [upd_ne _ _ hne]
        · show (upd s.bx id' (l2After C s id' c') id).batch = 0
          rw [upd_ne _ _ hne]
          exact hb0
  | @base l0 ts' dl' bx' ht hk he =>
      cases ht with
      | base hnt hs =>
          cases hs with
          | @ctm op c' hcs =>
              cases hcs with
              | @commit t _ _ hpv hlt _ _ =>
                  cases he with
                  | other _ _ =>
                      have hne : c.pv ≠ (C.T.X.W.tr t).old := by
                        have := hb.behind
                        omega
                      have hut : (upd s.ts.sys.ctm.ut (C.T.X.W.tr t).old t) c.pv =
                          s.ts.sys.ctm.ut c.pv := upd_ne _ _ hne
                      refine ⟨block_transfer hb rfl ?_ ?_ ?_ ?_ rfl rfl rfl rfl, Or.inl hb0⟩
                      · show s.ts.sys.ctm.pv ≤ (C.T.X.W.tr t).new
                        omega
                      · show (upd s.ts.sys.ctm.ut (C.T.X.W.tr t).old t) c.pv ≠ 0
                        rw [hut]
                        exact hb.committed
                      · show (C.T.X.W.tr (s.ts.sys.ctm.ut c.pv)).new ≤
                          (C.T.X.W.tr ((upd s.ts.sys.ctm.ut (C.T.X.W.tr t).old t) c.pv)).new
                        rw [hut]
                      · show (C.T.sched ((upd s.ts.sys.ctm.ut (C.T.X.W.tr t).old t) c.pv)).deadline
                          = (C.T.sched (s.ts.sys.ctm.ut c.pv)).deadline
                        rw [hut]
              | @replace e r he0 hr0 hslot _ _ hle _ _ =>
                  cases he with
                  | other _ _ =>
                      by_cases hv : c.pv = (C.T.X.W.tr e).old
                      · have hut : (upd s.ts.sys.ctm.ut (C.T.X.W.tr e).old r) c.pv = r := by
                          rw [hv]
                          exact upd_same _ _ _
                        have hold : s.ts.sys.ctm.ut c.pv = e := by
                          rw [hv]
                          exact hslot
                        refine ⟨block_transfer hb rfl le_rfl ?_ ?_ ?_ rfl rfl rfl rfl, Or.inl hb0⟩
                        · show (upd s.ts.sys.ctm.ut (C.T.X.W.tr e).old r) c.pv ≠ 0
                          rw [hut]
                          exact hr0
                        · show (C.T.X.W.tr (s.ts.sys.ctm.ut c.pv)).new ≤
                            (C.T.X.W.tr ((upd s.ts.sys.ctm.ut (C.T.X.W.tr e).old r) c.pv)).new
                          rw [hut, hold]
                          exact hle
                        · show (C.T.sched ((upd s.ts.sys.ctm.ut (C.T.X.W.tr e).old r)
                              c.pv)).deadline = (C.T.sched (s.ts.sys.ctm.ut c.pv)).deadline
                          rw [hut, hold]
                          exact hk
                      · have hut : (upd s.ts.sys.ctm.ut (C.T.X.W.tr e).old r) c.pv =
                            s.ts.sys.ctm.ut c.pv := upd_ne _ _ hv
                        refine ⟨block_transfer hb rfl le_rfl ?_ ?_ ?_ rfl rfl rfl rfl, Or.inl hb0⟩
                        · show (upd s.ts.sys.ctm.ut (C.T.X.W.tr e).old r) c.pv ≠ 0
                          rw [hut]
                          exact hb.committed
                        · show (C.T.X.W.tr (s.ts.sys.ctm.ut c.pv)).new ≤
                            (C.T.X.W.tr ((upd s.ts.sys.ctm.ut (C.T.X.W.tr e).old r) c.pv)).new
                          rw [hut]
                        · show (C.T.sched ((upd s.ts.sys.ctm.ut (C.T.X.W.tr e).old r)
                              c.pv)).deadline = (C.T.sched (s.ts.sys.ctm.ut c.pv)).deadline
                          rw [hut]
              | @legacyCommit R b _ hlt =>
                  have hne : c.pv ≠ s.ts.sys.ctm.pv := by
                    have := hb.behind
                    omega
                  cases he with
                  | legacyCommit =>
                      refine ⟨block_transfer hb rfl ?_ hb.committed le_rfl rfl ?_ ?_ rfl rfl,
                        Or.inl hb0⟩
                      · show s.ts.sys.ctm.pv ≤ C.T.X.W.relVersion R
                        omega
                      · show (upd s.ts.sys.ctm.legacy s.ts.sys.ctm.pv _) c.pv = _
                        exact upd_ne _ _ hne
                      · show (upd s.dl s.ts.sys.ctm.pv _) c.pv = s.dl c.pv
                        exact upd_ne _ _ hne
                  | other h1 _ => exact absurd rfl (h1 R b)
              | @legacyRecut v hut0 _ =>
                  cases he with
                  | other _ _ =>
                      have hne : c.pv ≠ v := fun h => hb.committed (h ▸ hut0)
                      refine ⟨block_transfer hb rfl le_rfl hb.committed le_rfl rfl ?_ rfl rfl rfl,
                        Or.inl hb0⟩
                      show (upd s.ts.sys.ctm.legacy v LegacyCut.opaque) c.pv = _
                      exact upd_ne _ _ hne
          | @genesis id' ρ hnone _ =>
              cases he with
              | other _ _ =>
                  have hne : id ≠ id' := by
                    rintro rfl
                    rw [hb.chain] at hnone
                    cases hnone
                  exact ⟨block_frame hb rfl (upd_ne _ _ hne) rfl rfl rfl, Or.inl hb0⟩
          | @migrateIn id' ρ v _ hnone _ =>
              cases he with
              | other _ _ =>
                  have hne : id ≠ id' := by
                    rintro rfl
                    rw [hb.chain] at hnone
                    cases hnone
                  exact ⟨block_frame hb rfl (upd_ne _ _ hne) rfl rfl rfl, Or.inl hb0⟩
          | transition _ _ _ _ _ => exact absurd trivial hnt
          | @bootstrapReset id' c' R ρ hc' hleg _ _ =>
              have hne : id ≠ id' := by
                rintro rfl
                rw [hb.chain] at hc'
                cases hc'
                rw [hb.noLegacy] at hleg
                cases hleg
              cases he with
              | bootstrapKeeps =>
                  exact ⟨block_frame hb rfl (upd_ne _ _ hne) rfl rfl rfl, Or.inl hb0⟩
              | bootstrapSets _ =>
                  refine ⟨block_frame hb rfl (upd_ne _ _ hne) rfl rfl ?_, Or.inl ?_⟩
                  · show (upd s.bx id' _ id).txHash = (s.bx id).txHash
                    rw [upd_ne _ _ hne]
                  · show (upd s.bx id' _ id).batch = 0
                    rw [upd_ne _ _ hne]
                    exact hb0
              | other _ h2 => exact absurd rfl (h2 id')
          | arbitraryCut _ _ _ => exact absurd trivial hna
  | setUpgradeTimestamp ht =>
      cases ht with
      | setUpgradeTimestamp _ _ _ _ => exact ⟨block_frame hb rfl rfl rfl rfl rfl, Or.inl hb0⟩
  | swapNotifier => exact ⟨block_frame hb rfl rfl rfl rfl rfl, Or.inl hb0⟩
  | @setRoles id' admin vs =>
      refine ⟨block_frame hb rfl rfl rfl ?_ rfl, Or.inl hb0⟩
      show (upd s.ts.aux id' _ id).slVersion = (s.ts.aux id).slVersion
      by_cases hid : id = id'
      · subst hid
        rw [upd_same]
      · rw [upd_ne _ _ hid]
  | @slMoves id' w w0 hw0 =>
      have hne : id ≠ id' := by
        rintro rfl
        rw [hb.onSL] at hw0
        cases hw0
      refine ⟨block_frame hb rfl rfl rfl ?_ rfl, Or.inl hb0⟩
      show (upd s.ts.aux id' _ id).slVersion = (s.ts.aux id).slVersion
      rw [upd_ne _ _ hne]
  | @reinit id' a x c' hc' hat _ =>
      have hne : id ≠ id' := by
        rintro rfl
        rw [hb.chain] at hc'
        cases hc'
        rcases hat with hat | hat
        · have := hb.behind
          omega
        · exact hat hb.onSL
      refine ⟨block_frame hb rfl rfl rfl ?_ ?_, Or.inl ?_⟩
      · show (upd s.ts.aux id' a id).slVersion = (s.ts.aux id).slVersion
        rw [upd_ne _ _ hne]
      · show (upd s.bx id' x id).txHash = (s.bx id).txHash
        rw [upd_ne _ _ hne]
      · show (upd s.bx id' x id).batch = 0
        rw [upd_ne _ _ hne]
        exact hb0
  | @commit id' τ' c' hc' hsl' hact =>
      by_cases hid : id = id'
      · subst hid
        rw [hb.chain] at hc'
        cases hc'
        refine ⟨block_frame hb rfl rfl rfl ?_ ?_, Or.inr ⟨τ', rfl, hact⟩⟩
        · show (upd s.ts.aux id _ id).slVersion = (s.ts.aux id).slVersion
          rw [upd_same]
        · show (upd s.bx id _ id).txHash = (s.bx id).txHash
          rw [upd_same]
          split_ifs <;> rfl
      · refine ⟨block_frame hb rfl rfl rfl ?_ ?_, Or.inl ?_⟩
        · show (upd s.ts.aux id' _ id).slVersion = (s.ts.aux id).slVersion
          rw [upd_ne _ _ hid]
        · show (upd s.bx id' _ id).txHash = (s.bx id).txHash
          rw [upd_ne _ _ hid]
        · show (upd s.bx id' _ id).batch = 0
          rw [upd_ne _ _ hid]
          exact hb0
  | @prove id' k _ _ =>
      by_cases hid : id = id'
      · subst hid
        refine ⟨block_frame hb rfl rfl rfl rfl ?_, Or.inl ?_⟩
        · show (upd s.bx id _ id).txHash = (s.bx id).txHash
          rw [upd_same]
        · show (upd s.bx id _ id).batch = 0
          rw [upd_same]
          exact hb0
      · refine ⟨block_frame hb rfl rfl rfl rfl ?_, Or.inl ?_⟩
        · show (upd s.bx id' _ id).txHash = (s.bx id).txHash
          rw [upd_ne _ _ hid]
        · show (upd s.bx id' _ id).batch = 0
          rw [upd_ne _ _ hid]
          exact hb0
  | @execute id' k _ _ =>
      by_cases hid : id = id'
      · subst hid
        have hkeep : ¬ ((s.bx id).batch ≠ 0 ∧ (s.bx id).batch ≤ (s.ts.aux id).executed + k) :=
          fun h => h.1 hb0
        refine ⟨block_frame hb rfl rfl rfl ?_ ?_, Or.inl ?_⟩
        · show (upd s.ts.aux id _ id).slVersion = (s.ts.aux id).slVersion
          rw [upd_same]
        · show (upd s.bx id _ id).txHash = (s.bx id).txHash
          rw [upd_same, ite_eq_right hkeep]
        · show (upd s.bx id _ id).batch = 0
          rw [upd_same, ite_eq_right hkeep]
          exact hb0
      · refine ⟨block_frame hb rfl rfl rfl ?_ ?_, Or.inl ?_⟩
        · show (upd s.ts.aux id' _ id).slVersion = (s.ts.aux id).slVersion
          rw [upd_ne _ _ hid]
        · show (upd s.bx id' _ id).txHash = (s.bx id).txHash
          rw [upd_ne _ _ hid]
        · show (upd s.bx id' _ id).batch = 0
          rw [upd_ne _ _ hid]
          exact hb0
  | @revertBatches id' n _ _ _ =>
      by_cases hid : id = id'
      · subst hid
        refine ⟨block_frame hb rfl rfl rfl ?_ ?_, Or.inl ?_⟩
        · show (upd s.ts.aux id _ id).slVersion = (s.ts.aux id).slVersion
          rw [upd_same]
        · show (upd s.bx id _ id).txHash = (s.bx id).txHash
          rw [upd_same]
        · show (upd s.bx id _ id).batch = 0
          rw [upd_same]
          show (if n < (s.bx id).batch then 0 else (s.bx id).batch) = 0
          split_ifs
          · rfl
          · exact hb0
      · refine ⟨block_frame hb rfl rfl rfl ?_ ?_, Or.inl ?_⟩
        · show (upd s.ts.aux id' _ id).slVersion = (s.ts.aux id).slVersion
          rw [upd_ne _ _ hid]
        · show (upd s.bx id' _ id).txHash = (s.bx id).txHash
          rw [upd_ne _ _ hid]
        · show (upd s.bx id' _ id).batch = 0
          rw [upd_ne _ _ hid]
          exact hb0
  | @setDeadline v t =>
      have hne : c.pv ≠ v := fun h => hnd t (h ▸ rfl)
      exact ⟨block_frame hb rfl rfl (upd_ne _ _ hne) rfl rfl, Or.inl hb0⟩

/-! ## The negative headline -/

/-- A `PendingBlock`ed chain whose version's deadline is before `τ` is in dead time at `τ`. -/
private lemma deadTime_of_block {C : PendingConfig} {s : PendingSys} {id : ChainId} {c : Chain}
    {x τ : ℕ} (hb : PendingBlock C s id c)
    (hx : versionDeadline C.T s.dl s.ts.sys.ctm c.pv = some x) (hxτ : x < τ) :
    PChainDeadTime C s id τ :=
  ⟨c, hb.chain, fun hact => absurd (hact x hx) (by omega), fun _ _ => hb.blocks⟩

/-- The invariant of the negative headline, along runs. -/
private lemma run_keeps {C : PendingConfig} {s s' : PendingSys} {ls : List PLabel} {id : ChainId}
    {c : Chain} {x τ : ℕ} (hw : PendingUnbatched C s id c)
    (hx : versionDeadline C.T s.dl s.ts.sys.ctm c.pv = some x) (hxτ : x < τ)
    (h : PRun C s ls s')
    (hl : ∀ l ∈ ls, ¬ l.isArbitrary ∧ (∀ t, l ≠ .setDeadline c.pv t) ∧ l.NotBefore τ) :
    PendingUnbatched C s' id c ∧ versionDeadline C.T s'.dl s'.ts.sys.ctm c.pv = some x := by
  induction h with
  | nil => exact ⟨hw, hx⟩
  | @cons s0 s1 s2 l ls hs _ ih =>
      obtain ⟨hna, hnd, hnb⟩ := hl l List.mem_cons_self
      obtain ⟨⟨hb', hd'⟩, hbatch⟩ := step_keeps hw hs hna hnd
      refine ih ⟨hb', ?_⟩ (hd'.trans hx) (fun l' hm => hl l' (List.mem_cons_of_mem _ hm))
      rcases hbatch with h0 | ⟨τ', rfl, hact⟩
      · exact h0
      · exfalso
        have h1 := hact x hx
        have h2 : τ ≤ τ' := hnb
        omega

theorem ExpiredPendingChainStaysInDeadTime : Properties.ExpiredPendingChainStaysInDeadTime := by
  intro C s s' ls id c x τ hw hx hxτ h hl
  obtain ⟨hw', hx'⟩ := run_keeps hw hx hxτ h hl
  exact ⟨hw', hx', fun τ' hτ' => deadTime_of_block hw'.1 hx' (by omega)⟩

/-! ## Ways out -/

theorem OnlyOverrideOrBreakGlassEndsDeadTime :
    Properties.OnlyOverrideOrBreakGlassEndsDeadTime := by
  intro C s s' l id c τ hw h hdead hnot
  by_contra hcon
  have hnd : ∀ t, l ≠ .setDeadline c.pv t := fun t ht => hcon (Or.inl ⟨t, ht⟩)
  have hna : ¬ l.isArbitrary := fun ha => hcon (Or.inr ha)
  obtain ⟨⟨hb', hd'⟩, -⟩ := step_keeps hw h hna hnd
  obtain ⟨c0, hc0, hna0, -⟩ := hdead
  rw [hw.1.chain] at hc0
  cases hc0
  apply hnot
  refine ⟨c, hb'.chain, fun hact => hna0 ?_, fun _ _ => hb'.blocks⟩
  intro y hy
  rw [← hd'] at hy
  exact hact y hy

theorem OverrideClearsPendingTx : Properties.OverrideClearsPendingTx := by
  intro C s id c t τ hc hsl hb0 hce hvc ht0 hτ
  have hdl : versionDeadline C.T (upd s.dl c.pv t) s.ts.sys.ctm c.pv = some t := by
    simp [versionDeadline, ht0]
  have hact : ∀ τ', τ' ≤ t → ProtocolVersionActive C.T (upd s.dl c.pv t) s.ts.sys.ctm c.pv τ' := by
    intro τ' hτ' y hy
    rw [hdl] at hy
    cases hy
    exact hτ'
  -- the four states
  let s1 : PendingSys := { s with dl := upd s.dl c.pv t }
  let s2 : PendingSys := s1.afterCommit id
  let s3 : PendingSys := s2.withBx id { s2.bx id with verified := (s2.bx id).verified + 1 }
  let s4 : PendingSys := s3.afterExecute id 1
  have h1 : PStep C s (.setDeadline c.pv t) s1 := PStep.setDeadline
  have h2 : PStep C s1 (.commit id τ) s2 := PStep.commit hc hsl (hact τ hτ)
  have hsl2 : (s2.ts.aux id).slVersion = none := by
    simp [s2, s1, PendingSys.afterCommit, PendingSys.withAux, PendingSys.withBx, hsl]
  have hc2 : (s2.ts.aux id).committed = (s.ts.aux id).committed + 1 := by
    simp [s2, s1, PendingSys.afterCommit, PendingSys.withAux, PendingSys.withBx]
  have hv2 : (s2.bx id).verified = (s.bx id).verified := by
    simp only [s2, s1, PendingSys.afterCommit, PendingSys.withAux, PendingSys.withBx, upd_same]
    split_ifs <;> rfl
  have he2 : (s2.ts.aux id).executed = (s.ts.aux id).executed := by
    simp [s2, s1, PendingSys.afterCommit, PendingSys.withAux, PendingSys.withBx]
  have hbx2 : (s2.bx id).batch =
      (if (s.bx id).txHash ≠ 0 then (s.ts.aux id).committed + 1 else 0) := by
    simp only [s2, s1, PendingSys.afterCommit, PendingSys.withAux, PendingSys.withBx, upd_same]
    by_cases hh : (s.bx id).txHash = 0
    · simp [hh, hb0]
    · simp [hh, hb0]
  have htx2 : (s2.bx id).txHash = (s.bx id).txHash := by
    simp only [s2, s1, PendingSys.afterCommit, PendingSys.withAux, PendingSys.withBx, upd_same]
    split_ifs <;> rfl
  have h3 : PStep C s2 (.prove id 1) s3 := PStep.prove hsl2 (by omega)
  have hsl3 : (s3.ts.aux id).slVersion = none := hsl2
  have he3 : (s3.ts.aux id).executed = (s.ts.aux id).executed := he2
  have hv3 : (s3.bx id).verified = (s.bx id).verified + 1 := by
    simp only [s3, PendingSys.withBx, upd_same]
    rw [hv2]
  have h4 : PStep C s3 (.execute id 1) s4 := PStep.execute hsl3 (by omega)
  refine ⟨s4, PRun.cons h1 (PRun.cons h2 (PRun.cons h3 (PRun.cons h4 PRun.nil))), rfl, ?_, ?_, ?_,
    hact τ hτ⟩
  · -- the transaction is cleared, or there was none
    have hb3 : (s3.bx id).batch = (s2.bx id).batch := by simp [s3, PendingSys.withBx]
    have ht3 : (s3.bx id).txHash = (s2.bx id).txHash := by simp [s3, PendingSys.withBx]
    simp only [s4, PendingSys.afterExecute, PendingSys.withAux, PendingSys.withBx, upd_same]
    split_ifs with hcond
    · rfl
    · rw [ht3, htx2]
      by_contra hh
      apply hcond
      rw [hb3, hbx2, ite_eq_left hh, he3]
      exact ⟨by omega, by omega⟩
  · have hb3 : (s3.bx id).batch = (s2.bx id).batch := by simp [s3, PendingSys.withBx]
    simp only [s4, PendingSys.afterExecute, PendingSys.withAux, PendingSys.withBx, upd_same]
    split_ifs with hcond
    · rfl
    · rw [hb3, hbx2]
      split_ifs with hh
      · exfalso
        apply hcond
        rw [hb3, hbx2, ite_eq_left hh, he3]
        exact ⟨by omega, by omega⟩
      · rfl
  · have hc3 : (s3.ts.aux id).committed = (s.ts.aux id).committed + 1 := hc2
    simp only [s4, PendingSys.afterExecute, PendingSys.withAux, PendingSys.withBx, upd_same]
    show (s3.ts.aux id).committed = (s3.ts.aux id).executed + 1
    omega

/-! ## No dead time without a pending transaction -/

theorem NoDeadTimeWithoutPendingTx : Properties.NoDeadTimeWithoutPendingTx := by
  intro C s s' ls hI hR hV hP h hl hw hv id c hc hut hd hb hsl hext hpatch
  obtain ⟨ls', hrun, hcov⟩ := PendingRunIsATimedRun C s s' ls h
  have hl' : ∀ l ∈ ls', ¬ l.isArbitrary :=
    timed_labels hcov (Q := fun l => ¬ l.isArbitrary)
      (fun l' hn => by cases l' <;> first | exact fun h => h | exact absurd rfl (hn _))
      (fun _ h => h) hl
  have hw' : ∀ l ∈ ls', l.InstallsWf C.T.X.W :=
    timed_labels hcov (Q := fun l => l.InstallsWf C.T.X.W)
      (fun l' hn => by cases l' <;> first | trivial | exact absurd rfl (hn _))
      (fun _ h => h) hw
  have hv' : ∀ l ∈ ls', l.CommitsValidSchedule C.T :=
    timed_labels hcov (Q := fun l => l.CommitsValidSchedule C.T)
      (fun l' hn => by cases l' <;> first | trivial | exact absurd rfl (hn _))
      (fun _ h => h) hv
  obtain ⟨-, hwin, hact, hdir, hctm⟩ :=
    ValidatedTimedRunsHaveNoDeadTime C.T s'.dl s.ts s'.ts ls' hI hR hV hrun hl' hw' hv' id c hc
      hut hd hb hsl
  have hP' : PendingInv s' := PendingInvAlongRuns C s s' ls hP h
  have hgate : L2Gate C s' id c := by
    refine ⟨fun _ hnp => ?_, fun _ hl2 hp => ?_⟩
    · have htx : (s'.bx id).txHash = 0 := hext.resolve_right hnp
      refine ⟨htx, ?_⟩
      by_contra hb0
      exact hP' id hb0 htx
    · rw [hpatch hp] at hl2
      cases hl2
  have hlift : ∀ path caller τ,
      TimedStep C.T s'.ts (.upgrade id path caller τ)
        { s'.ts with sys := s'.ts.sys.crossEdge C.T.X.W id c } →
      PStep C s' (.upgrade id path caller τ) (s'.crossed C id c) :=
    fun _ _ _ ht => PStep.upgrade ht hc hgate
  have hwin' : ∀ τ, ProtocolVersionActive C.T s'.dl s'.ts.sys.ctm c.pv τ ∨
      (PStep C s' (.upgrade id (.direct c.pv) (s'.ts.aux id).admin τ) (s'.crossed C id c) ∧
        PStep C s' (.upgrade id (.ctm c.pv) C.T.ctmOwner τ) (s'.crossed C id c)) := by
    intro τ
    rcases hwin τ with ha | ⟨h1, h2⟩
    · exact Or.inl ha
    · exact Or.inr ⟨hlift _ _ _ h1, hlift _ _ _ h2⟩
  refine ⟨fun τ hdead => ?_, hwin', hact, hlift _ _ _ hdir, hlift _ _ _ hctm⟩
  obtain ⟨c', hc', hna, hno⟩ := hdead
  rw [hc] at hc'
  cases hc'
  rcases hwin' τ with ha | ⟨h1, _⟩
  · exact hna ha
  · exact hno _ _ ⟨_, h1⟩

/-! ## The witness states

Every state the witness runs reach, written out as the steps produce it. `ctm2` is the CTM after
`pwSetup` (`300` and `600` committed, at `0.3.0`), `ctmP` the CTM after `pwPatchSetup` (`300` and
`700` committed, at `0.2.1`). Chain `0` is at `0.1.0` in `ch1` and at `0.2.0` in `ch2`. -/

private lemma pwNodup100 : ((pwWorld.relRows 100).map Prod.fst).Nodup := by decide
private lemma pwNodup200 : ((pwWorld.relRows 200).map Prod.fst).Nodup := by decide
private lemma pwNodup250 : ((pwWorld.relRows 250).map Prod.fst).Nodup := by decide
private lemma pwNodup260 : ((pwWorld.relRows 260).map Prod.fst).Nodup := by decide

private def ctm0 : CTM := initState pwWorld 100

private def ctm1 : CTM :=
  ⟨v020, 200, upd (fun _ => 0) v010 300, fun _ => LegacyCut.none,
    upd (upd (fun _ => 0) v010 100) v020 200⟩

private def ctm2 : CTM :=
  ⟨v030, 250, upd (upd (fun _ => 0) v010 300) v020 600, fun _ => LegacyCut.none,
    upd (upd (upd (fun _ => 0) v010 100) v020 200) v030 250⟩

private def ctmP : CTM :=
  ⟨v021, 260, upd (upd (fun _ => 0) v010 300) v020 700, fun _ => LegacyCut.none,
    upd (upd (upd (fun _ => 0) v010 100) v020 200) v021 260⟩

private def ch1 : ChainId → Option Chain :=
  upd (fun _ => none) 0 (some ⟨v010, rowsRouting (pwRows 100)⟩)

private def ch2 : ChainId → Option Chain := upd ch1 0 (some ⟨v020, rowsRouting (pwRows 200)⟩)

private def aux0 : ChainId → DiamondAux := fun _ => ⟨0, fun _ => false, 0, 0, none⟩

private def aux1 : ChainId → DiamondAux := upd aux0 0 wTimingAux

private def bx0 : ChainId → BatchAux := fun _ => ⟨0, 0, 0⟩

private def bx1 : ChainId → BatchAux := upd bx0 0 ⟨0, 0, 0⟩

private def bx2 : ChainId → BatchAux := upd bx1 0 ⟨0, 7, 0⟩

/-- After genesis of chain `0`. -/
private def stG : PendingSys := ⟨⟨⟨ctm0, ch1⟩, aux0, fun _ _ => 0⟩, fun _ => 0, bx0⟩
/-- After its initialization. -/
private def stR : PendingSys := ⟨⟨⟨ctm0, ch1⟩, aux1, fun _ _ => 0⟩, fun _ => 0, bx1⟩
/-- After committing `300`. -/
private def stC1 : PendingSys := ⟨⟨⟨ctm1, ch1⟩, aux1, fun _ _ => 0⟩, fun _ => 0, bx1⟩
/-- The end of `pwSetup`. -/
private def stSet : PendingSys := ⟨⟨⟨ctm2, ch1⟩, aux1, fun _ _ => 0⟩, fun _ => 0, bx1⟩
/-- After the late upgrade. -/
private def stLate : PendingSys := ⟨⟨⟨ctm2, ch2⟩, aux1, fun _ _ => 0⟩, fun _ => 0, bx2⟩
/-- The end of `pwPatchSetup`. -/
private def stPSet : PendingSys := ⟨⟨⟨ctmP, ch1⟩, aux1, fun _ _ => 0⟩, fun _ => 0, bx1⟩
/-- After the late upgrade, with the patch committed at `0.2.0`. -/
private def stPLate : PendingSys := ⟨⟨⟨ctmP, ch2⟩, aux1, fun _ _ => 0⟩, fun _ => 0, bx2⟩

/-- Chain `0`'s state at `0.2.0`. -/
private def c020 : Chain := ⟨v020, rowsRouting (pwRows 200)⟩

/-- A step that is not a legacy commit and not a bootstrap crossing. -/
private lemma baseOther {s : PendingSys} {l : Label} (h1 : ∀ R b, l ≠ .ctm (.legacyCommit R b))
    (h2 : ∀ id, l ≠ .bootstrapReset id) : BaseEffect s l s.dl s.bx :=
  BaseEffect.other h1 h2

private lemma prun_append {C : PendingConfig} {s s' s'' : PendingSys} {l1 l2 : List PLabel}
    (h1 : PRun C s l1 s') (h2 : PRun C s' l2 s'') : PRun C s (l1 ++ l2) s'' := by
  induction h1 with
  | nil => exact h2
  | cons hs _ ih => exact PRun.cons hs (ih h2)

/-! ### The setup runs -/

private lemma step_genesis0 : PStep pwConfig pwSys0 (.base (.genesis 0)) stG :=
  PStep.base (TimedStep.base (fun h => h) (Step.genesis rfl (addAll_empty_eq pwNodup100))) trivial
    (baseOther (fun _ _ h => by cases h) (fun _ h => by cases h))

private lemma step_reinit0 : PStep pwConfig stG (.reinit 0 wTimingAux ⟨0, 0, 0⟩) stR :=
  PStep.reinit (c := ⟨v010, rowsRouting (pwRows 100)⟩) rfl (Or.inl rfl) (fun h => absurd rfl h)

private lemma step_commit300 : PStep pwConfig stR (.base (.ctm (.commit 300))) stC1 :=
  PStep.base (TimedStep.base (fun h => h) (Step.ctm (CStep.commit (t := 300) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)))) trivial
    (baseOther (fun _ _ h => by cases h) (fun _ h => by cases h))

private lemma step_commit600 : PStep pwConfig stC1 (.base (.ctm (.commit 600))) stSet :=
  PStep.base (TimedStep.base (fun h => h) (Step.ctm (CStep.commit (t := 600) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)))) trivial
    (baseOther (fun _ _ h => by cases h) (fun _ h => by cases h))

private lemma step_commit700 : PStep pwConfig stC1 (.base (.ctm (.commit 700))) stPSet :=
  PStep.base (TimedStep.base (fun h => h) (Step.ctm (CStep.commit (t := 700) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)))) trivial
    (baseOther (fun _ _ h => by cases h) (fun _ h => by cases h))

private lemma run_setup : PRun pwConfig pwSys0 pwSetup stSet :=
  PRun.cons step_genesis0 (PRun.cons step_reinit0 (PRun.cons step_commit300
    (PRun.cons step_commit600 PRun.nil)))

private lemma run_patchSetup : PRun pwConfig pwSys0 pwPatchSetup stPSet :=
  PRun.cons step_genesis0 (PRun.cons step_reinit0 (PRun.cons step_commit300
    (PRun.cons step_commit700 PRun.nil)))

private lemma notPatch010 : ¬ PatchOnly v010 (pwWorld.tr 300).new := by
  unfold PatchOnly minorOf semverMinorUnit
  decide

/-- The late upgrade of chain `0` across `300`, at `25`, through the CTM, after `pwSetup`. -/
private lemma step_late : PStep pwConfig stSet pwLateUpgrade stLate := by
  have hrt : Step pwWorld ⟨ctm2, ch1⟩ (.transition 0) ⟨ctm2, ch2⟩ :=
    Step.transition (c := ⟨v010, rowsRouting (pwRows 100)⟩) rfl (by decide) rfl
      (applyDerived_rows_eq pwNodup100 pwNodup200) (by decide)
  have hl2 : l2After pwConfig stSet 0 ⟨v010, rowsRouting (pwRows 100)⟩ = ⟨0, 7, 0⟩ := by
    simp only [l2After]
    rw [ite_eq_left ⟨rfl, rfl⟩]
    rfl
  have h := PStep.upgrade (C := pwConfig) (s := stSet) (id := 0) (path := .ctm v010) (caller := 1)
    (τ := 25) (c := ⟨v010, rowsRouting (pwRows 100)⟩)
    (TimedStep.ctm rfl
      ⟨Or.inr (Or.inl rfl), ⟨_, rfl, rfl⟩, fun _ h => absurd rfl h, rfl, hrt, by decide,
        fun w hw => by cases hw⟩)
    rfl ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => notPatch010⟩
  rw [hl2] at h
  exact h

/-- The same upgrade after `pwPatchSetup`. -/
private lemma step_patchLate : PStep pwConfig stPSet pwLateUpgrade stPLate := by
  have hrt : Step pwWorld ⟨ctmP, ch1⟩ (.transition 0) ⟨ctmP, ch2⟩ :=
    Step.transition (c := ⟨v010, rowsRouting (pwRows 100)⟩) rfl (by decide) rfl
      (applyDerived_rows_eq pwNodup100 pwNodup200) (by decide)
  have hl2 : l2After pwConfig stPSet 0 ⟨v010, rowsRouting (pwRows 100)⟩ = ⟨0, 7, 0⟩ := by
    simp only [l2After]
    rw [ite_eq_left ⟨rfl, rfl⟩]
    rfl
  have h := PStep.upgrade (C := pwConfig) (s := stPSet) (id := 0) (path := .ctm v010)
    (caller := 1) (τ := 25) (c := ⟨v010, rowsRouting (pwRows 100)⟩)
    (TimedStep.ctm rfl
      ⟨Or.inr (Or.inl rfl), ⟨_, rfl, rfl⟩, fun _ h => absurd rfl h, rfl, hrt, by decide,
        fun w hw => by cases hw⟩)
    rfl ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => notPatch010⟩
  rw [hl2] at h
  exact h

private lemma run_late : PRun pwConfig pwSys0 (pwSetup ++ [pwLateUpgrade]) stLate :=
  prun_append run_setup (PRun.cons step_late PRun.nil)

private lemma run_patchLate : PRun pwConfig pwSys0 (pwPatchSetup ++ [pwLateUpgrade]) stPLate :=
  prun_append run_patchSetup (PRun.cons step_patchLate PRun.nil)

/-! ### Facts about the witness states -/

private lemma not_active_of {T : TimedConfig} {d : ℕ → ℕ} {s : CTM} {v τ x : ℕ}
    (h : versionDeadline T d s v = some x) (hx : x < τ) : ¬ ProtocolVersionActive T d s v τ :=
  fun ha => absurd (ha x h) (by omega)

private lemma active_of_none {T : TimedConfig} {d : ℕ → ℕ} {s : CTM} {v τ : ℕ}
    (h : versionDeadline T d s v = none) : ProtocolVersionActive T d s v τ := by
  intro x hx
  rw [h] at hx
  cases hx

private lemma active_of {T : TimedConfig} {d : ℕ → ℕ} {s : CTM} {v τ x : ℕ}
    (h : versionDeadline T d s v = some x) (hx : τ ≤ x) : ProtocolVersionActive T d s v τ := by
  intro y hy
  rw [h] at hy
  cases hy
  exact hx

private lemma deadline_late :
    versionDeadline pwTimed stLate.dl stLate.ts.sys.ctm v020 = some 20 := by
  decide

private lemma unbatched_late : PendingUnbatched pwConfig stLate 0 c020 :=
  ⟨⟨rfl, by decide, by decide, by decide, rfl, by decide, rfl⟩, rfl⟩

private lemma dead_late : PChainDeadTime pwConfig stLate 0 25 :=
  deadTime_of_block unbatched_late.1 deadline_late (by decide)

private lemma start_premises :
    SysInv pwTimed.X.W pwSys0.ts.sys ∧ RecordedReleasesWf pwTimed.X.W pwSys0.ts.sys.ctm ∧
      SlotSchedulesValid pwTimed pwSys0.ts.sys.ctm ∧ PendingInv pwSys0 :=
  ⟨FreshSystemSatisfiesInvariant pwWorld 100 (by decide),
    (StartingStatesMeetLivenessPremises pwWorld 100).1 pwNodup100,
    fun _ hv => absurd rfl hv, fun _ h => absurd rfl h⟩

private lemma setup_labels : ∀ l ∈ pwSetup,
    ¬ l.isArbitrary ∧ l.InstallsWf pwTimed.X.W ∧ l.CommitsValidSchedule pwTimed := by
  intro l hl
  simp only [pwSetup, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · exact ⟨fun h => h, trivial, trivial⟩
  · exact ⟨fun h => h, trivial, trivial⟩
  · exact ⟨fun h => h, pwNodup200, ⟨by decide, by decide⟩⟩
  · exact ⟨fun h => h, pwNodup250, ⟨by decide, by decide⟩⟩

private lemma patchSetup_labels : ∀ l ∈ pwPatchSetup,
    ¬ l.isArbitrary ∧ l.InstallsWf pwTimed.X.W ∧ l.CommitsValidSchedule pwTimed := by
  intro l hl
  simp only [pwPatchSetup, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · exact ⟨fun h => h, trivial, trivial⟩
  · exact ⟨fun h => h, trivial, trivial⟩
  · exact ⟨fun h => h, pwNodup200, ⟨by decide, by decide⟩⟩
  · exact ⟨fun h => h, pwNodup260, ⟨by decide, by decide⟩⟩

private lemma late_labels {ls : List PLabel}
    (h : ∀ l ∈ ls, ¬ l.isArbitrary ∧ l.InstallsWf pwTimed.X.W ∧ l.CommitsValidSchedule pwTimed) :
    ∀ l ∈ ls ++ [pwLateUpgrade],
      ¬ l.isArbitrary ∧ l.InstallsWf pwTimed.X.W ∧ l.CommitsValidSchedule pwTimed := by
  intro l hl
  rcases List.mem_append.mp hl with hm | hm
  · exact h l hm
  · rw [List.mem_singleton] at hm
    subst hm
    exact ⟨fun h => h, trivial, trivial⟩

/-! ## The premises of the negative headline are met -/

private def stI1 : PendingSys :=
  ⟨⟨⟨ctm2, ch2⟩, aux1, fun _ _ => 0⟩, upd (fun _ => 0) v010 30, bx2⟩
private def stI2 : PendingSys :=
  ⟨⟨⟨ctm2, ch2⟩, aux1, setNotifierEntry (fun _ _ => 0) 0 v020 30⟩, upd (fun _ => 0) v010 30, bx2⟩
private def ch3 : ChainId → Option Chain := upd ch2 1 (some ⟨v030, rowsRouting (pwRows 250)⟩)
private def stI3 : PendingSys :=
  ⟨⟨⟨ctm2, ch3⟩, aux1, setNotifierEntry (fun _ _ => 0) 0 v020 30⟩, upd (fun _ => 0) v010 30, bx2⟩
private def stI4 : PendingSys :=
  ⟨⟨⟨ctm2, ch3⟩, upd aux1 1 wTimingAux, setNotifierEntry (fun _ _ => 0) 0 v020 30⟩,
    upd (fun _ => 0) v010 30, upd bx2 1 ⟨0, 0, 0⟩⟩
private def stI5 : PendingSys :=
  ⟨⟨⟨ctm2, ch3⟩, upd (upd aux1 1 wTimingAux) 1 { wTimingAux with committed := 1 },
      setNotifierEntry (fun _ _ => 0) 0 v020 30⟩,
    upd (fun _ => 0) v010 30, upd (upd bx2 1 ⟨0, 0, 0⟩) 1 ⟨0, 0, 0⟩⟩

private lemma run_idle : PRun pwConfig stLate pwIdle stI5 := by
  have h1 : PStep pwConfig stLate (.setDeadline v010 30) stI1 := PStep.setDeadline
  have h2 : PStep pwConfig stI1 (.setUpgradeTimestamp 0 3 30) stI2 :=
    PStep.setUpgradeTimestamp (TimedStep.setUpgradeTimestamp (c := c020) rfl rfl (by decide)
      (Or.inl (by decide)))
  have h3 : PStep pwConfig stI2 (.base (.genesis 1)) stI3 :=
    PStep.base (TimedStep.base (fun h => h) (Step.genesis rfl (addAll_empty_eq pwNodup250)))
      trivial (baseOther (fun _ _ h => by cases h) (fun _ h => by cases h))
  have h4 : PStep pwConfig stI3 (.reinit 1 wTimingAux ⟨0, 0, 0⟩) stI4 :=
    PStep.reinit (c := ⟨v030, rowsRouting (pwRows 250)⟩) rfl (Or.inl rfl) (fun h => absurd rfl h)
  have hact : ProtocolVersionActive pwTimed stI4.dl stI4.ts.sys.ctm v030 30 :=
    active_of_none (by decide)
  have h5 : PStep pwConfig stI4 (.commit 1 30) stI5 :=
    PStep.commit (c := ⟨v030, rowsRouting (pwRows 250)⟩) rfl rfl hact
  exact PRun.cons h1 (PRun.cons h2 (PRun.cons h3 (PRun.cons h4 (PRun.cons h5 PRun.nil))))

private lemma idle_labels :
    ∀ l ∈ pwIdle, ¬ l.isArbitrary ∧ (∀ t, l ≠ .setDeadline v020 t) ∧ l.NotBefore 25 := by
  intro l hl
  simp only [pwIdle, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl
  · refine ⟨fun h => h, fun t h => ?_, trivial⟩
    injection h with h1
    exact absurd h1 (by decide)
  · exact ⟨fun h => h, fun _ h => (by cases h), trivial⟩
  · exact ⟨fun h => h, fun _ h => (by cases h), trivial⟩
  · exact ⟨fun h => h, fun _ h => (by cases h), trivial⟩
  · exact ⟨fun h => h, fun _ h => (by cases h), (by decide : 25 ≤ 30)⟩

theorem ExpiredPendingChainWitness : Properties.ExpiredPendingChainWitness := by
  obtain ⟨hw, -, hdead⟩ := ExpiredPendingChainStaysInDeadTime pwConfig stLate stI5 pwIdle 0 c020
    20 25 unbatched_late deadline_late (by decide) run_idle idle_labels
  exact ⟨stLate, stI5, run_late, unbatched_late, deadline_late, run_idle, idle_labels, rfl, rfl, hw,
    hdead 25 le_rfl⟩

/-! ## The concrete instance -/

private lemma validEdge300 : ValidEdge pwConfig 300 :=
  ⟨⟨by decide, by decide⟩, by decide,
    fun hp => absurd hp (by unfold PatchOnly minorOf semverMinorUnit; decide)⟩

private lemma validEdge600 : ValidEdge pwConfig 600 :=
  ⟨⟨by decide, by decide⟩, by decide,
    fun hp => absurd hp (by unfold PatchOnly minorOf semverMinorUnit; decide)⟩

theorem LateUpgradeLandsInDeadTime : Properties.LateUpgradeLandsInDeadTime := by
  refine ⟨validEdge300, validEdge600, by decide, by decide, rfl, rfl, stSet, stLate, run_setup,
    rfl, by decide, by decide, rfl, rfl, rfl, rfl, rfl, rfl,
    not_active_of (x := 20) (by decide) (by decide), ?_, step_late, rfl, rfl, deadline_late, ?_⟩
  · rintro ⟨c, -, -, hno⟩
    exact hno (.ctm v010) 1 ⟨stLate, step_late⟩
  · intro ls s' h hl τ' hτ'
    obtain ⟨hw, hx, -⟩ := ExpiredPendingChainStaysInDeadTime pwConfig stLate s' ls 0 c020 20 25
      unbatched_late deadline_late (by decide) h hl
    exact deadTime_of_block hw.1 hx (by omega)

/-! ## No dead time without a pending transaction: witnesses and the countermodel -/

theorem NoDeadTimeWithoutPendingTxWitness : Properties.NoDeadTimeWithoutPendingTxWitness := by
  obtain ⟨hI, hR, hV, hP⟩ := start_premises
  have hnp : ¬ PatchOnly v010 (stSet.ts.sys.edge pwTimed.X.W v010).new := by
    unfold PatchOnly minorOf semverMinorUnit
    decide
  obtain ⟨hnd, hwin, -, -, -⟩ := NoDeadTimeWithoutPendingTx pwConfig pwSys0 stSet pwSetup hI hR hV
    hP run_setup (fun l hl => (setup_labels l hl).1) (fun l hl => (setup_labels l hl).2.1)
    (fun l hl => (setup_labels l hl).2.2) 0 ⟨v010, rowsRouting (pwRows 100)⟩ rfl (by decide) rfl
    rfl (fun w hw => by cases hw) (Or.inl rfl) (fun hp => absurd hp hnp)
  have hna : ¬ ProtocolVersionActive pwTimed stSet.dl stSet.ts.sys.ctm v010 25 :=
    not_active_of (x := 20) (by decide) (by decide)
  have hdir := ((hwin 25).resolve_left hna).1
  exact ⟨hI, hR, hV, hP, setup_labels, stSet, run_setup, rfl, by decide, rfl, rfl, rfl, rfl, hnp,
    hna, hdir, hnd⟩

theorem NoDeadTimeAcrossPatchWithPendingTx : Properties.NoDeadTimeAcrossPatchWithPendingTx := by
  obtain ⟨hI, hR, hV, hP⟩ := start_premises
  have hl := late_labels patchSetup_labels
  have hpo : PatchOnly v020 (stPLate.ts.sys.edge pwTimed.X.W v020).new := by
    unfold PatchOnly minorOf semverMinorUnit
    decide
  obtain ⟨hnd, hwin, -, -, -⟩ := NoDeadTimeWithoutPendingTx pwConfig pwSys0 stPLate
    (pwPatchSetup ++ [pwLateUpgrade]) hI hR hV hP run_patchLate (fun l h => (hl l h).1)
    (fun l h => (hl l h).2.1) (fun l h => (hl l h).2.2) 0 c020 rfl (by decide) rfl rfl
    (fun w hw => by cases hw) (Or.inr hpo) (fun _ => rfl)
  have hna : ¬ ProtocolVersionActive pwTimed stPLate.dl stPLate.ts.sys.ctm v020 25 :=
    not_active_of (x := 20) (by decide) (by decide)
  have hdir := ((hwin 25).resolve_left hna).1
  exact ⟨hl, stPLate, run_patchLate, rfl, by decide, rfl, rfl, rfl, rfl, hpo, rfl, hna, hdir, rfl,
    hnd⟩

theorem NoDeadTimeNeedsItsPendingTxPremise : Properties.NoDeadTimeNeedsItsPendingTxPremise := by
  intro H
  obtain ⟨hI, hR, hV, hP⟩ := start_premises
  have hl := late_labels setup_labels
  have hnp : ¬ PatchOnly v020 (stLate.ts.sys.edge pwTimed.X.W v020).new := by
    unfold PatchOnly minorOf semverMinorUnit
    decide
  exact H pwConfig pwSys0 stLate (pwSetup ++ [pwLateUpgrade]) hI hR hV hP run_late
    (fun l h => (hl l h).1) (fun l h => (hl l h).2.1) (fun l h => (hl l h).2.2) 0 c020 rfl
    (by decide) rfl rfl (fun w hw => by cases hw) (fun hp => absurd hp hnp) 25 dead_late

/-! ## Ways out: the instances -/

private def dlO : ℕ → ℕ := upd (fun _ => 0) v020 100
private def auxC : ChainId → DiamondAux := upd aux1 0 { wTimingAux with committed := 1 }
private def auxE : ChainId → DiamondAux :=
  upd auxC 0 { wTimingAux with committed := 1, executed := 1 }
private def bxC : ChainId → BatchAux := upd bx2 0 ⟨0, 7, 1⟩
private def bxP : ChainId → BatchAux := upd bxC 0 ⟨1, 7, 1⟩
private def bxE : ChainId → BatchAux := upd bxP 0 ⟨1, 0, 0⟩
private def ch4 : ChainId → Option Chain := upd ch2 0 (some ⟨v030, rowsRouting (pwRows 250)⟩)

/-- After the override. -/
private def stO : PendingSys := ⟨⟨⟨ctm2, ch2⟩, aux1, fun _ _ => 0⟩, dlO, bx2⟩
/-- After the commit. -/
private def stOC : PendingSys := ⟨⟨⟨ctm2, ch2⟩, auxC, fun _ _ => 0⟩, dlO, bxC⟩
/-- After proving. -/
private def stOP : PendingSys := ⟨⟨⟨ctm2, ch2⟩, auxC, fun _ _ => 0⟩, dlO, bxP⟩
/-- After executing. -/
private def stOE : PendingSys := ⟨⟨⟨ctm2, ch2⟩, auxE, fun _ _ => 0⟩, dlO, bxE⟩
/-- After the upgrade across `600`. -/
private def stOU : PendingSys := ⟨⟨⟨ctm2, ch4⟩, auxE, fun _ _ => 0⟩, dlO, upd bxE 0 ⟨1, 7, 0⟩⟩

private lemma step_override : PStep pwConfig stLate (.setDeadline v020 100) stO := PStep.setDeadline

private lemma step_commitO : PStep pwConfig stO (.commit 0 30) stOC :=
  PStep.commit (c := c020) rfl rfl (active_of (x := 100) (by decide) (by decide))

private lemma step_proveO : PStep pwConfig stOC (.prove 0 1) stOP :=
  PStep.prove rfl (by decide)

private lemma step_executeO : PStep pwConfig stOP (.execute 0 1) stOE :=
  PStep.execute rfl (by decide)

private lemma step_upgradeO : PStep pwConfig stOE (.upgrade 0 (.ctm v020) 1 30) stOU := by
  have hrt : Step pwWorld ⟨ctm2, ch2⟩ (.transition 0) ⟨ctm2, ch4⟩ :=
    Step.transition (c := c020) rfl (by decide) rfl (applyDerived_rows_eq pwNodup200 pwNodup250)
      (by decide)
  have hpatch : ¬ PatchOnly v020 (pwWorld.tr 600).new := by
    unfold PatchOnly minorOf semverMinorUnit
    decide
  have hl2 : l2After pwConfig stOE 0 c020 = ⟨1, 7, 0⟩ := by
    simp only [l2After]
    rw [ite_eq_left ⟨rfl, rfl⟩]
    rfl
  have h := PStep.upgrade (C := pwConfig) (s := stOE) (id := 0) (path := .ctm v020) (caller := 1)
    (τ := 30) (c := c020)
    (TimedStep.ctm rfl
      ⟨Or.inr (Or.inl rfl), ⟨_, rfl, rfl⟩, fun _ h => absurd rfl h, rfl, hrt, by decide,
        fun w hw => by cases hw⟩)
    rfl ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => hpatch⟩
  rw [hl2] at h
  exact h

theorem OverrideRecoversExpiredPendingChain : Properties.OverrideRecoversExpiredPendingChain := by
  refine ⟨stLate, stO, stOC, stOU, run_late, unbatched_late, rfl, rfl, dead_late, step_override, ?_,
    step_commitO, rfl, rfl,
    PRun.cons step_override (PRun.cons step_commitO (PRun.cons step_proveO
      (PRun.cons step_executeO (PRun.cons step_upgradeO PRun.nil)))),
    rfl, rfl, rfl, rfl, ?_⟩
  · rintro ⟨c, hc, hna, -⟩
    have hcc : c = c020 := (Option.some.inj (hc.symm.trans rfl) :)
    subst hcc
    exact hna (active_of (x := 100) (by decide) (by decide))
  · rintro τ ⟨c, hc, hna, -⟩
    have hcc : c = ⟨v030, rowsRouting (pwRows 250)⟩ := (Option.some.inj (hc.symm.trans rfl) :)
    subst hcc
    exact hna (active_of_none (by decide))

theorem BreakGlassEndsDeadTime : Properties.BreakGlassEndsDeadTime := by
  have hbg : PStep pwConfig stLate (.base (.arbitraryCut 0 v030 (rowsRouting (pwRows 250))))
      ⟨⟨⟨ctm2, ch4⟩, aux1, fun _ _ => 0⟩, fun _ => 0, bx2⟩ :=
    PStep.base (TimedStep.base (fun h => h) (Step.arbitraryCut (c := c020) v030 _ rfl)) trivial
      (baseOther (fun _ _ h => by cases h) (fun _ h => by cases h))
  refine ⟨stLate, _, run_late, unbatched_late, dead_late, hbg, ?_⟩
  rintro ⟨c, hc, hna, -⟩
  have hcc : c = ⟨v030, rowsRouting (pwRows 250)⟩ := (Option.some.inj (hc.symm.trans rfl) :)
  subst hcc
  exact hna (active_of_none (by decide))

end Contracts.ChainTypeManager.PendingL2UpgradeAtV35
