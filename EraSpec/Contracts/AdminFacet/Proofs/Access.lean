import EraSpec.Contracts.AdminFacet.Properties.Access
import EraSpec.Contracts.AdminFacet.Proofs.Basic

/-!
# Proofs: access control of the `AdminFacet`

Each `Properties.X` of `EraSpec.Contracts.AdminFacet.Properties.Access` is proved as `X`.
-/

namespace Contracts.AdminFacet

/-! ## One-step lemmas lifted to `Step` -/

section StepLemmas

variable {K : Config} {w w' : World} {l : Label}

theorem step_admin (h : Step K w l w') (hc : l.runsCut = false) :
    w'.st.admin = w.st.admin ∨
      (∃ τ, l = .call ⟨w.st.pendingAdmin, τ, .acceptAdmin⟩ ∧ w'.st.admin = w.st.pendingAdmin) := by
  cases h with
  | call hs =>
    rename_i c s'
    rcases exec_admin (call_exec hs) hc with h1 | ⟨he, hsnd, h2⟩
    · exact Or.inl h1
    · right; refine ⟨c.time, ?_, h2⟩
      rcases c with ⟨a, τ, en⟩; simp only at he hsnd; subst he hsnd; rfl
  | env => exact Or.inl rfl
  | foreign hf => exact Or.inl hf.admin

theorem step_pending (h : Step K w l w') (hc : l.runsCut = false) :
    w'.st.pendingAdmin = w.st.pendingAdmin ∨
      (∃ a τ, l = .call ⟨a, τ, .setPendingAdmin w'.st.pendingAdmin⟩) ∨
      w'.st.pendingAdmin = 0 := by
  cases h with
  | call hs =>
    rename_i c s'
    rcases exec_pending (call_exec hs) hc with h1 | h1 | ⟨_, h2⟩
    · exact Or.inl h1
    · right; left; refine ⟨c.sender, c.time, ?_⟩
      rcases c with ⟨a, τ, en⟩; simp only at h1; subst h1; rfl
    · exact Or.inr (Or.inr h2)
  | env => exact Or.inl rfl
  | foreign hf => exact Or.inl hf.pendingAdmin

theorem step_ctm (h : Step K w l w') (hc : l.runsCut = false) :
    w'.st.chainTypeManager = w.st.chainTypeManager := by
  cases h with
  | call hs => exact (exec_fixed (call_exec hs) hc).1
  | env => rfl
  | foreign hf => exact hf.chainTypeManager

theorem step_validators (h : Step K w l w') (hc : l.runsCut = false) (x : Address) :
    w'.st.validators x = w.st.validators x ∨
      ∃ τ, l = .call ⟨w.st.chainTypeManager, τ, .setValidator x (w'.st.validators x)⟩ := by
  cases h with
  | call hs =>
    rename_i c s'
    rcases exec_validators (call_exec hs) hc x with h1 | ⟨he, hsnd⟩
    · exact Or.inl h1
    · right; refine ⟨c.time, ?_⟩
      rcases c with ⟨a, τ, en⟩; simp only at he hsnd; subst he hsnd; rfl
  | env => exact Or.inl rfl
  | foreign hf => exact Or.inl (by rw [hf.validators])

theorem step_frozen (h : Step K w l w') (hc : l.runsCut = false) :
    w'.st.frozen = w.st.frozen ∨
      (∃ τ, l = .call ⟨w.st.chainTypeManager, τ, .freezeDiamond⟩ ∧ w.st.frozen = false ∧
        w'.st.frozen = true) ∨
      (∃ τ, l = .call ⟨w.st.chainTypeManager, τ, .unfreezeDiamond⟩ ∧ w.st.frozen = true ∧
        w'.st.frozen = false) := by
  cases h with
  | call hs =>
    rename_i c s'
    rcases exec_frozen (call_exec hs) hc with h1 | ⟨he, hsnd, h2, h3⟩ | ⟨he, hsnd, h2, h3⟩
    · exact Or.inl h1
    · right; left; refine ⟨c.time, ?_, h2, h3⟩
      rcases c with ⟨a, τ, en⟩; simp only at he hsnd; subst he hsnd; rfl
    · right; right; refine ⟨c.time, ?_, h2, h3⟩
      rcases c with ⟨a, τ, en⟩; simp only at he hsnd; subst he hsnd; rfl
  | env => exact Or.inl rfl
  | foreign hf => exact Or.inl hf.frozen

end StepLemmas

/-! ## One-step properties -/

theorem every_entry_checks_its_role : Properties.EveryEntryChecksItsRole := by
  intro K e s s' c h
  have h := call_exec h
  rcases c with ⟨snd, τ, en⟩
  cases en <;> simp only [exec, Role, onlyL1, onlySettlementLayer, noUnverifiedBatches,
    req_eq_some] at h ⊢ <;> tauto

theorem caller_matters_only_through_role : Properties.CallerMattersOnlyThroughRole := by
  intro K e s s' c b h hb hx
  have hr : Role e s c.sender c.entry := every_entry_checks_its_role K e s s' c h
  unfold call at h ⊢
  rcases c with ⟨a, τ, en⟩
  simp only at hb hr hx h ⊢
  rw [req_eq_some] at h
  obtain ⟨hfz, h⟩ := h
  rw [req_eq_some]
  refine ⟨hfz, ?_⟩
  cases en
  case upgradeChainFromVersion ch v =>
    simp only [Role] at hb hr
    have hbp : b = s.admin ∨ b = s.chainTypeManager := by
      rcases hx with hx | hx
      · exact absurd rfl (hx ch v)
      · exact hx
    simp only [exec] at h ⊢
    rw [req_eq_some] at h
    obtain ⟨_, h⟩ := h
    rw [req_eq_some]
    refine ⟨hb, ?_⟩
    cases hcut : e.upgradeCutForVersion s.chainTypeManager v with
    | none => simp [hcut] at h
    | some cut =>
      simp only [hcut] at h ⊢
      unfold upgradeWithCut at h ⊢
      rw [req_eq_some] at h ⊢
      obtain ⟨hv, h⟩ := h
      refine ⟨hv, ?_⟩
      rw [req_eq_some] at h ⊢
      obtain ⟨_, h⟩ := h
      refine ⟨?_, h⟩
      intro hne
      rcases hbp with rfl | rfl <;> simp at hne
  all_goals
    simp only [Role] at hb hr
    first
    | (subst hb; subst hr; exact h)
    | (simp only [exec] at h ⊢; simp_all [req])

theorem validator_upgrade_waits_for_schedule : Properties.ValidatorUpgradeWaitsForSchedule := by
  intro K e s s' a τ ch v h ha hc
  have h := call_exec h
  simp only [exec, req_eq_some] at h
  obtain ⟨hr, h⟩ := h
  cases hcut : e.upgradeCutForVersion s.chainTypeManager v with
  | none => simp [hcut] at h
  | some cut =>
    simp only [hcut] at h
    unfold upgradeWithCut at h
    rw [req_eq_some, req_eq_some] at h
    obtain ⟨_, hg, _⟩ := h
    refine ⟨?_, hg ⟨ha, hc⟩⟩
    rcases hr with h | h | h
    · exact absurd h ha
    · exact absurd h hc
    · exact h

theorem admin_handover_is_two_step : Properties.AdminHandoverIsTwoStep := by
  intro K e s a τ h1 h2
  refine ⟨fun p => ?_, ?_⟩
  · simp only [Entry.sel] at h1
    simp only [call, exec, req, Entry.sel, h1, ite_true, not_false_eq_true]
  · simp only [Entry.sel] at h2
    simp only [call, exec, req, Entry.sel, h2, ite_true, not_false_eq_true]

theorem freeze_unfreeze_exact : Properties.FreezeUnfreezeExact := by
  intro K e s a τ
  refine ⟨?_, ?_⟩
  · simp only [call, exec, req, Entry.sel]
    by_cases hf : s.frozen = true <;> by_cases ha : a = s.chainTypeManager <;>
      by_cases hz : s.freezable 0x27ae4c16 = true <;> simp [hf, ha, hz]
  · simp only [call, exec, req, Entry.sel]
    by_cases hf : s.frozen = true <;> by_cases ha : a = s.chainTypeManager <;>
      by_cases hz : s.freezable 0x17338945 = true <;> simp [hf, ha, hz]

/-! ## Run-level properties -/

theorem admin_changes_only_by_acceptance : Properties.AdminChangesOnlyByAcceptance := by
  intro K w w' ls hr
  induction hr with
  | nil => intro _ _ h; exact absurd rfl h
  | @cons w w₁ w₂ l ls hs _ ih =>
    intro hnc hnz hne
    have hl : l.runsCut = false := hnc l List.mem_cons_self
    have ih := ih (fun l' hl' => hnc l' (List.mem_cons_of_mem _ hl'))
      (fun c hc => hnz c (List.mem_cons_of_mem _ hc))
    by_cases h21 : w₂.st.admin = w₁.st.admin
    · -- the head step changed the admin
      have h1 : w₁.st.admin ≠ w.st.admin := h21 ▸ hne
      rcases step_admin hs hl with h | ⟨τ, rfl, hadm⟩
      · exact absurd h h1
      · refine ⟨⟨τ, ?_⟩, Or.inl (h21.trans hadm)⟩
        rw [h21, hadm]; exact List.mem_cons_self
    · obtain ⟨⟨τ, hacc⟩, hnom⟩ := ih h21
      refine ⟨⟨τ, List.mem_cons_of_mem _ hacc⟩, ?_⟩
      rcases hnom with hp | ⟨a, τ', hm⟩
      · rcases step_pending hs hl with h | ⟨a, τ', rfl⟩ | h
        · exact Or.inl (hp.trans h)
        · exact Or.inr ⟨a, τ', by rw [hp]; exact List.mem_cons_self⟩
        · exact absurd (hp.trans h)
            (hnz _ (List.mem_cons_of_mem _ hacc))
      · exact Or.inr ⟨a, τ', List.mem_cons_of_mem _ hm⟩

theorem validators_change_only_by_ctm : Properties.ValidatorsChangeOnlyByCTM := by
  intro K w w' ls hr
  induction hr with
  | nil => intro _; exact ⟨rfl, fun x h => absurd rfl h⟩
  | @cons w w₁ w₂ l ls hs _ ih =>
    intro hnc
    have hl : l.runsCut = false := hnc l List.mem_cons_self
    obtain ⟨hctm, ih⟩ := ih (fun l' hl' => hnc l' (List.mem_cons_of_mem _ hl'))
    have hctm1 := step_ctm hs hl
    refine ⟨hctm.trans hctm1, fun x hx => ?_⟩
    by_cases h21 : w₂.st.validators x = w₁.st.validators x
    · rcases step_validators hs hl x with h | ⟨τ, rfl⟩
      · exact absurd (h21.trans h) hx
      · exact ⟨τ, by rw [h21]; exact List.mem_cons_self⟩
    · obtain ⟨τ, hm⟩ := ih x h21
      exact ⟨τ, by rw [← hctm1]; exact List.mem_cons_of_mem _ hm⟩

theorem freeze_only_by_ctm : Properties.FreezeOnlyByCTM := by
  intro K w w' ls hr
  induction hr with
  | nil => intro _; exact ⟨fun h1 h2 => by simp_all, fun h1 h2 => by simp_all⟩
  | @cons w w₁ w₂ l ls hs _ ih =>
    intro hnc
    have hl : l.runsCut = false := hnc l List.mem_cons_self
    obtain ⟨ihf, ihu⟩ := ih (fun l' hl' => hnc l' (List.mem_cons_of_mem _ hl'))
    have hctm1 := step_ctm hs hl
    refine ⟨fun h0 h2 => ?_, fun h0 h2 => ?_⟩
    · cases h1 : w₁.st.frozen
      · obtain ⟨τ, hm⟩ := ihf h1 h2
        exact ⟨τ, by rw [← hctm1]; exact List.mem_cons_of_mem _ hm⟩
      · rcases step_frozen hs hl with h | ⟨τ, rfl, _, _⟩ | ⟨τ, _, h3, _⟩
        · simp_all
        · exact ⟨τ, List.mem_cons_self⟩
        · simp_all
    · cases h1 : w₁.st.frozen
      · rcases step_frozen hs hl with h | ⟨τ, _, h3, _⟩ | ⟨τ, rfl, _, _⟩
        · simp_all
        · simp_all
        · exact ⟨τ, List.mem_cons_self⟩
      · obtain ⟨τ, hm⟩ := ihu h1 h2
        exact ⟨τ, by rw [← hctm1]; exact List.mem_cons_of_mem _ hm⟩

/-- The selector of every cut entry is one of the three cut selectors. -/
theorem runsCut_sel {en : Entry} (h : en.runsCut = true) :
    en.sel = (Entry.upgradeChainFromVersion 0 0).sel ∨ en.sel = (Entry.executeUpgrade ⟨[], 0, 0⟩).sel ∨
      en.sel = Entry.genesisUpgrade.sel := by
  cases en <;> simp_all [Entry.runsCut, Entry.sel]

theorem freezable_unfreeze_strands_the_chain : Properties.FreezableUnfreezeStrandsTheChain := by
  intro K w w' ls hr
  induction hr with
  | nil => intro h _ _ _ _; exact h
  | @cons w w₁ w₂ l ls hs _ ih =>
    intro hf hu hup hex hgen
    -- the step keeps the diamond frozen and the freezability table
    have key : w₁.st.frozen = true ∧ w₁.st.freezable = w.st.freezable := by
      cases hs with
      | @call c s' hc =>
        have hblk := call_not_blocked hc
        have hsel : w.st.freezable c.entry.sel = false := by
          cases h' : w.st.freezable c.entry.sel <;> simp_all
        cases hcut : c.entry.runsCut
        · have hx := exec_frozen (call_exec hc) hcut
          have hfx := (exec_fixed (call_exec hc) hcut).2.2.2.1
          refine ⟨?_, hfx⟩
          rcases hx with h | ⟨_, _, h, _⟩ | ⟨he, _, _, _⟩
          · simpa [h] using hf
          · simp_all
          · rw [he] at hsel; simp_all
        · rcases runsCut_sel hcut with h | h | h <;> rw [h] at hsel <;> simp_all
      | env => exact ⟨hf, rfl⟩
      | foreign hfo => exact ⟨hfo.frozen ▸ hf, hfo.freezable⟩
    obtain ⟨h1, h2⟩ := key
    exact ih h1 (by rw [h2]; exact hu) (by rw [h2]; exact hup) (by rw [h2]; exact hex)
      (by rw [h2]; exact hgen)

/-! ## Witnesses -/

/-- A fresh chain: admin `1`, CTM `9`, everything else zero. -/
def freshState : State where
  admin := 1
  pendingAdmin := 0
  chainTypeManager := 9
  validators := fun _ => false
  frozen := false
  freezable := fun _ => false
  protocolVersion := 0
  verifier := 0
  settlementLayer := 0
  priorityTxMaxGasLimit := 0
  zksyncOSMaxTxGasLimit := 0
  l1TxFiltering := false
  largeContracts := false
  feeParams := ⟨0, 0, 0, 0, 0, 0⟩
  multNominator := 0
  multDenominator := 1
  lastFeeParamsUpdate := 0
  lastTokenMultiplierUpdate := 0
  transactionFilterer := 0
  l1DAValidator := 0
  l2DAScheme := 0
  pubdataContent := .fullPubdata
  isPermanentRollup := false
  secondProofSystemRequired := false
  disabledProofSystems := 0
  priorityMode := ⟨false, false, 0, 0⟩
  pausedDepositsTimestamp := 0
  ptStartIndex := 0
  ptNextLeafIndex := 0
  ptUnprocessedIndex := 0
  requestTimestamp := fun _ => 0
  totalBatchesCommitted := 0
  totalBatchesVerified := 0
  totalBatchesExecuted := 0
  upgradeTxHash := 0
  upgradeBatchNumber := 0

/-- An environment in which nothing is committed and every external read is zero. -/
def nullEnv : Env where
  upgradeCutForVersion := fun _ _ => none
  upgradeTimestamp := fun _ _ => 0
  l1GenesisUpgrade := fun _ => 0
  genesisTxHash := fun _ _ => 0
  bridgehubOwner := 0
  isPairAllowed := fun _ _ => false
  getProofMode := fun _ _ => 0
  cutContext := 0

/-- An L1 deployment whose cuts all revert. -/
def nullConfig : Config where
  onL1 := true
  runCut := fun _ _ _ _ => none

/-- An L1 deployment whose every cut raises the protocol version by one. -/
def raiseConfig : Config where
  onL1 := true
  runCut := fun _ _ _ s => some { s with protocolVersion := s.protocolVersion + 1 }

/-- The CTM has a cut committed for every version, the notifier's time is `10`, every DA pair is
allowed and every verifier reports multi-proof mode. -/
def openEnv : Env :=
  { nullEnv with
    upgradeCutForVersion := fun _ _ => some ⟨[], 43, 0⟩
    upgradeTimestamp := fun _ _ => 10
    isPairAllowed := fun _ _ => true
    getProofMode := fun _ _ => ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE }

/-- `freshState` after the Mailbox enqueued one priority transaction at time `100`. -/
def queuedState : State :=
  { freshState with ptNextLeafIndex := 1, requestTimestamp := fun i => if i = 0 then 100 else 0 }

theorem every_entry_succeeds_somewhere : Properties.EveryEntrySucceedsSomewhere := by
  intro en
  cases en with
  | setPendingAdmin _ => exact ⟨.setPendingAdmin 5, raiseConfig, openEnv, freshState, _, 1, 0, rfl, rfl⟩
  | acceptAdmin =>
    exact ⟨.acceptAdmin, raiseConfig, openEnv, { freshState with pendingAdmin := 2 }, _, 2, 0,
      rfl, rfl⟩
  | setValidator _ _ => exact ⟨.setValidator 7 true, raiseConfig, openEnv, freshState, _, 9, 0, rfl, rfl⟩
  | setPriorityTxMaxGasLimit _ =>
    exact ⟨.setPriorityTxMaxGasLimit 1000, raiseConfig, openEnv, freshState, _, 9, 0, rfl, rfl⟩
  | setZKsyncOSMaxTxGasLimit _ =>
    exact ⟨.setZKsyncOSMaxTxGasLimit (2 ^ 24), raiseConfig, openEnv, freshState, _, 1, 0, rfl, rfl⟩
  | setZKsyncOSL1TxFiltering _ =>
    exact ⟨.setZKsyncOSL1TxFiltering true, raiseConfig, openEnv, freshState, _, 1, 0, rfl, rfl⟩
  | setZKsyncOSLargeContractsEnabled _ =>
    exact ⟨.setZKsyncOSLargeContractsEnabled true, raiseConfig, openEnv, freshState, _, 1, 0,
      rfl, rfl⟩
  | changeFeeParams _ =>
    exact ⟨.changeFeeParams ⟨0, 0, 0, 0, 0, 5⟩, raiseConfig, openEnv, freshState, _, 1, 1000,
      rfl, rfl⟩
  | setTokenMultiplier _ _ =>
    exact ⟨.setTokenMultiplier 2 1, raiseConfig, openEnv, freshState, _, 1, 1000, rfl, rfl⟩
  | setPubdataPricingMode _ =>
    exact ⟨.setPubdataPricingMode 1, raiseConfig, openEnv, freshState, _, 1, 0, rfl, rfl⟩
  | setTransactionFilterer _ =>
    exact ⟨.setTransactionFilterer 5, raiseConfig, openEnv, freshState, _, 1, 0, rfl, rfl⟩
  | setDAValidatorPair _ _ =>
    exact ⟨.setDAValidatorPair 3 2, raiseConfig, openEnv, freshState, _, 1, 0, rfl, rfl⟩
  | setPubdataContent _ =>
    exact ⟨.setPubdataContent .logsOnly, raiseConfig, openEnv, freshState, _, 1, 0, rfl, rfl⟩
  | setProofSystemStatus _ _ =>
    exact ⟨.setProofSystemStatus PROOF_SYSTEM_ZISK false, raiseConfig, openEnv, freshState, _, 1,
      0, rfl, rfl⟩
  | makePermanentRollup =>
    exact ⟨.makePermanentRollup, raiseConfig, openEnv, freshState, _, 1, 0, rfl, rfl⟩
  | permanentlyRequireSecondProofSystem =>
    exact ⟨.permanentlyRequireSecondProofSystem, raiseConfig, openEnv, freshState, _, 1, 0,
      rfl, rfl⟩
  | setPriorityModeTransactionFilterer _ =>
    exact ⟨.setPriorityModeTransactionFilterer 5, raiseConfig, openEnv, freshState, _, 9, 0,
      rfl, rfl⟩
  | permanentlyAllowPriorityMode =>
    exact ⟨.permanentlyAllowPriorityMode, raiseConfig, openEnv, queuedState, _, 1, 0, rfl, rfl⟩
  | deactivatePriorityMode =>
    exact ⟨.deactivatePriorityMode, raiseConfig, openEnv,
      { queuedState with isPermanentRollup := true, priorityMode := ⟨true, true, 0, 0⟩ }, _, 9, 0,
      rfl, rfl⟩
  | activatePriorityMode =>
    refine ⟨.activatePriorityMode, raiseConfig, openEnv,
      { queuedState with isPermanentRollup := true, priorityMode := ⟨true, false, 0, 0⟩ },
      { queuedState with isPermanentRollup := true, priorityMode := ⟨true, true, 0, 0⟩ }, 7,
      100 + PRIORITY_EXPIRATION, rfl, ?_⟩
    simp [call, exec, req, onlySettlementLayer, onlyL1, revertBatches, queuedState, freshState,
      State.firstUnprocessed, raiseConfig]
  | upgradeChainFromVersion _ _ =>
    exact ⟨.upgradeChainFromVersion 0 0, raiseConfig, openEnv, freshState, _, 1, 0, rfl, rfl⟩
  | executeUpgrade _ =>
    exact ⟨.executeUpgrade ⟨[], 43, 0⟩, raiseConfig, openEnv, freshState, _, 9, 0, rfl, rfl⟩
  | genesisUpgrade => exact ⟨.genesisUpgrade, raiseConfig, openEnv, freshState, _, 9, 0, rfl, rfl⟩
  | freezeDiamond => exact ⟨.freezeDiamond, raiseConfig, openEnv, freshState, _, 9, 0, rfl, rfl⟩
  | unfreezeDiamond =>
    exact ⟨.unfreezeDiamond, raiseConfig, openEnv, { freshState with frozen := true }, _, 9, 0,
      rfl, rfl⟩

/-- `freshState` with address `7` a validator. -/
def validatorState : State :=
  { freshState with validators := fun x => if x = 7 then true else false }

theorem validator_upgrade_witness : Properties.ValidatorUpgradeWitness :=
  ⟨raiseConfig, openEnv, validatorState, { validatorState with protocolVersion := 1 }, 7, 10, 0, 0,
    rfl, by decide, by decide, by decide, Or.inl rfl, rfl⟩

theorem admin_handover_witness : Properties.AdminHandoverWitness := by
  refine ⟨nullConfig, ⟨{ freshState with frozen := true }, nullEnv⟩,
    ⟨{ freshState with frozen := true, admin := 2, pendingAdmin := 0 }, nullEnv⟩,
    [.call ⟨1, 0, .setPendingAdmin 2⟩, .call ⟨2, 0, .acceptAdmin⟩], ?_, ?_, ?_, rfl, rfl, rfl,
    rfl, rfl, rfl⟩
  · refine Run.cons (w₁ := ⟨{ freshState with frozen := true, pendingAdmin := 2 }, nullEnv⟩)
      (Step.call rfl) (Run.cons (Step.call rfl) (Run.nil _))
  · intro l hl; simp at hl; rcases hl with rfl | rfl <;> rfl
  · intro c hc; simp at hc; rcases hc with rfl | rfl <;> decide

/-- `freshState` after another facet committed a batch. -/
def committedState : State := { freshState with totalBatchesCommitted := 1 }

/-- `nullEnv` after the Bridgehub's ownership moved to `5`. -/
def ownerEnv : Env := { nullEnv with bridgehubOwner := 5 }

theorem validator_change_witness : Properties.ValidatorChangeWitness := by
  refine ⟨nullConfig, ⟨freshState, nullEnv⟩,
    ⟨{ committedState with validators := fun x => if x = 7 then true else freshState.validators x },
      ownerEnv⟩,
    [.env ownerEnv, .foreign committedState, .call ⟨9, 0, .setValidator 7 true⟩], 7, ?_, ?_,
    ⟨ownerEnv, by simp⟩, ⟨committedState, by simp⟩, rfl, rfl⟩
  · refine Run.cons (Step.env _) ?_
    refine Run.cons (Step.foreign ⟨rfl, fun h => h⟩) ?_
    exact Run.cons (Step.call rfl) (Run.nil _)
  · intro l hl; simp at hl; rcases hl with rfl | rfl | rfl <;> rfl

theorem freeze_witness : Properties.FreezeWitness := by
  refine ⟨nullConfig, ⟨freshState, nullEnv⟩, ⟨{ freshState with frozen := true }, nullEnv⟩,
    ⟨{ freshState with pendingAdmin := 2 }, nullEnv⟩,
    [.call ⟨9, 0, .freezeDiamond⟩],
    [.call ⟨1, 0, .setPendingAdmin 2⟩, .call ⟨9, 0, .unfreezeDiamond⟩],
    Run.cons (Step.call rfl) (Run.nil _), ?_, ?_, by decide, rfl, rfl, rfl⟩
  · refine Run.cons (w₁ := ⟨{ freshState with frozen := true, pendingAdmin := 2 }, nullEnv⟩)
      (Step.call rfl) ?_
    exact Run.cons (Step.call rfl) (Run.nil _)
  · intro l hl; simp at hl; rcases hl with rfl | rfl | rfl <;> rfl

/-- A frozen diamond whose selectors are all freezable. -/
def strandedState : State := { freshState with frozen := true, freezable := fun _ => true }

/-- `strandedState` after the Migrator paused deposits at time `1000`. -/
def strandedPausedState : State := { strandedState with pausedDepositsTimestamp := 1000 }

theorem stranded_chain_witness : Properties.StrandedChainWitness := by
  refine ⟨nullConfig, ⟨strandedState, nullEnv⟩, ⟨strandedPausedState, ownerEnv⟩,
    [.env ownerEnv, .foreign strandedPausedState], ?_, rfl, rfl, rfl, rfl, rfl,
    ⟨ownerEnv, by simp⟩, ⟨strandedPausedState, by simp⟩, by decide⟩
  refine Run.cons (Step.env _) ?_
  exact Run.cons (Step.foreign ⟨rfl, fun h => h⟩) (Run.nil _)

/-! ## Certificates -/

theorem EveryEntryChecksItsRole : Properties.EveryEntryChecksItsRole :=
  every_entry_checks_its_role
theorem CallerMattersOnlyThroughRole : Properties.CallerMattersOnlyThroughRole :=
  caller_matters_only_through_role
theorem ValidatorUpgradeWaitsForSchedule : Properties.ValidatorUpgradeWaitsForSchedule :=
  validator_upgrade_waits_for_schedule
theorem AdminHandoverIsTwoStep : Properties.AdminHandoverIsTwoStep :=
  admin_handover_is_two_step
theorem AdminChangesOnlyByAcceptance : Properties.AdminChangesOnlyByAcceptance :=
  admin_changes_only_by_acceptance
theorem ValidatorsChangeOnlyByCTM : Properties.ValidatorsChangeOnlyByCTM :=
  validators_change_only_by_ctm
theorem FreezeOnlyByCTM : Properties.FreezeOnlyByCTM :=
  freeze_only_by_ctm
theorem FreezeUnfreezeExact : Properties.FreezeUnfreezeExact :=
  freeze_unfreeze_exact
theorem FreezableUnfreezeStrandsTheChain : Properties.FreezableUnfreezeStrandsTheChain :=
  freezable_unfreeze_strands_the_chain
theorem EveryEntrySucceedsSomewhere : Properties.EveryEntrySucceedsSomewhere :=
  every_entry_succeeds_somewhere
theorem ValidatorUpgradeWitness : Properties.ValidatorUpgradeWitness :=
  validator_upgrade_witness
theorem AdminHandoverWitness : Properties.AdminHandoverWitness :=
  admin_handover_witness
theorem ValidatorChangeWitness : Properties.ValidatorChangeWitness :=
  validator_change_witness
theorem FreezeWitness : Properties.FreezeWitness :=
  freeze_witness
theorem StrandedChainWitness : Properties.StrandedChainWitness :=
  stranded_chain_witness

end Contracts.AdminFacet
