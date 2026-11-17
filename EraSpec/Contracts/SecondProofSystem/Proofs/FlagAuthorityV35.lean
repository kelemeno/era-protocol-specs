import EraSpec.Contracts.SecondProofSystem.Properties.FlagAuthorityV35

/-!
# Proofs: the second-proof-system flag is one-way, and ZiSK-off is the Bridgehub owner's

Every step statement goes through one inversion, `step_inv`: a successful call that is not a
break-glass cut is `setProofSystemStatus(Zisk, _)` by the caller the rule names, or the admin's
`permanentlyRequireSecondProofSystem`, or a call that leaves the flag and the mask as they are
and either keeps the verifier or leaves one that reports multi-proof mode for the zero mask.
The run statements are inductions over `ReachWith` (`reach_inv`). The mask facts are checked
over all 256 masks by `decide`; the witnesses evaluate concrete calls by `decide`.
-/

namespace Contracts.SecondProofSystem.FlagAuthorityV35

open Clear

/-! ## Mask arithmetic -/

private theorem forall_uint8 {P : UInt8 → Prop} (h : ∀ i : Fin 256, P (UInt8.ofFin i))
    (m : UInt8) : P m := by
  have := h m.toFin
  simpa using this

set_option maxRecDepth 100000 in
private theorem mask_enable_zisk : ∀ m : UInt8, (m &&& ~~~ziskBit) &&& ziskBit = 0 := by
  apply forall_uint8
  decide

set_option maxRecDepth 100000 in
private theorem mask_disable_zisk : ∀ m : UInt8, (m ||| ziskBit) &&& ziskBit ≠ 0 := by
  apply forall_uint8
  decide

set_option maxRecDepth 100000 in
private theorem mask_enable_other :
    ∀ m : UInt8, (m &&& ~~~ziskBit) &&& ~~~ziskBit = m &&& ~~~ziskBit := by
  apply forall_uint8
  decide

set_option maxRecDepth 100000 in
private theorem mask_disable_other :
    ∀ m : UInt8, (m ||| ziskBit) &&& ~~~ziskBit = m &&& ~~~ziskBit := by
  apply forall_uint8
  decide

set_option maxRecDepth 100000 in
private theorem airbender_via_other :
    ∀ m : UInt8, m &&& ProofSystem.airbender.bit =
      (m &&& ~~~ziskBit) &&& ProofSystem.airbender.bit := by
  apply forall_uint8
  decide

set_option maxRecDepth 100000 in
private theorem multiProof_iff :
    ∀ m : UInt8, multiProofGetProofMode m = some MULTI_PROOF_TYPE ↔ m = 0 := by
  apply forall_uint8
  decide

private theorem newMask_other (m : UInt8) (en : Bool) :
    newMask m .zisk en &&& ~~~ziskBit = m &&& ~~~ziskBit := by
  cases en
  · exact mask_disable_other m
  · exact mask_enable_other m

private theorem multiProofEnv_reportsZisk (v : Address) : ReportsZisk multiProofEnv v := by
  intro m h
  have hz : m = 0 := (multiProof_iff m).mp h
  rw [hz]
  decide

/-! ## The definitions, call by call -/

private theorem ite_none_eq_some_iff {α : Type} {p : Prop} [Decidable p] {x : Option α} {a : α} :
    (if p then none else x) = some a ↔ ¬ p ∧ x = some a := by
  by_cases hp : p <;> simp [hp]

private theorem step_setPendingAdmin (rule : St → Bool → Address) (E : Env) (c a : Address)
    (s : St) :
    stepWith rule E c (.setPendingAdmin a) s =
      if c ≠ s.admin then none else some { s with pendingAdmin := a } := rfl

private theorem step_acceptAdmin (rule : St → Bool → Address) (E : Env) (c : Address) (s : St) :
    stepWith rule E c .acceptAdmin s =
      if c ≠ s.pendingAdmin then none
      else some { s with admin := s.pendingAdmin, pendingAdmin := 0 } := rfl

private theorem step_setStatus (rule : St → Bool → Address) (E : Env) (c : Address)
    (p : ProofSystem) (en : Bool) (s : St) :
    stepWith rule E c (.setProofSystemStatus p en) s =
      if c ≠ rule s en then none
      else if p ≠ .zisk then none
      else some { s with disabledProofSystems := newMask s.disabledProofSystems p en } := rfl

private theorem step_require (rule : St → Bool → Address) (E : Env) (c : Address) (s : St) :
    stepWith rule E c .permanentlyRequireSecondProofSystem s =
      if c ≠ s.admin then none
      else if s.settlementLayer ≠ 0 then none
      else if s.secondProofSystemRequired = true then none
      else if E.proofMode s.verifier s.disabledProofSystems ≠ some MULTI_PROOF_TYPE then none
      else some { s with secondProofSystemRequired := true } := rfl

private theorem step_upgrade (rule : St → Bool → Address) (E : Env) (c : Address) (i : Init)
    (s : St) :
    stepWith rule E c (.upgradeChainFromVersion i) s = executeDiamondCut E i s := rfl

private theorem step_execute (rule : St → Bool → Address) (E : Env) (c : Address) (i : Init)
    (s : St) :
    stepWith rule E c (.executeUpgrade i) s =
      if c ≠ s.chainTypeManager then none else executeDiamondCut E i s := rfl

private theorem step_genesis (rule : St → Bool → Address) (E : Env) (c : Address) (i : Init)
    (s : St) :
    stepWith rule E c (.genesisUpgrade i) s =
      if c ≠ s.chainTypeManager then none else executeDiamondCut E i s := rfl

private theorem callerRule_false_flag {s : St} (hf : s.secondProofSystemRequired = true) :
    callerRule s false = s.bridgehubOwner := by
  simp [callerRule, hf]

private theorem callerRule_true (s : St) : callerRule s true = s.admin := by
  simp [callerRule]

private theorem flagged_iff {s : St} :
    FlaggedZiskOff s ↔ s.secondProofSystemRequired = true ∧ ziskOff s := Iff.rfl

private theorem gate_iff {E : Env} {s : St} :
    InteropSecondProofGate E s ↔
      s.secondProofSystemRequired = true ∧
        E.proofMode s.verifier s.disabledProofSystems = some MULTI_PROOF_TYPE := Iff.rfl

private theorem setStatus_zisk_iff {rule : St → Bool → Address} {E : Env} {c : Address}
    {en : Bool} {s s' : St} :
    stepWith rule E c (.setProofSystemStatus .zisk en) s = some s' ↔
      c = rule s en ∧
        s' = { s with disabledProofSystems := newMask s.disabledProofSystems .zisk en } := by
  rw [step_setStatus, ite_none_eq_some_iff, ite_none_eq_some_iff]
  constructor
  · rintro ⟨h1, -, h3⟩
    exact ⟨not_not.mp h1, (Option.some.inj h3).symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨not_not.mpr h1, not_not.mpr rfl, congrArg some h2.symm⟩

private theorem require_iff {rule : St → Bool → Address} {E : Env} {c : Address} {s s' : St} :
    stepWith rule E c .permanentlyRequireSecondProofSystem s = some s' ↔
      (c = s.admin ∧ s.settlementLayer = 0 ∧ s.secondProofSystemRequired = false ∧
        E.proofMode s.verifier s.disabledProofSystems = some MULTI_PROOF_TYPE ∧
        s' = { s with secondProofSystemRequired := true }) := by
  rw [step_require, ite_none_eq_some_iff, ite_none_eq_some_iff, ite_none_eq_some_iff,
    ite_none_eq_some_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4, h⟩
    exact ⟨not_not.mp h1, not_not.mp h2, Bool.eq_false_iff.mpr h3, not_not.mp h4,
      (Option.some.inj h).symm⟩
  · rintro ⟨h1, h2, h3, h4, h⟩
    exact ⟨not_not.mpr h1, not_not.mpr h2, Bool.eq_false_iff.mp h3, not_not.mpr h4,
      congrArg some h.symm⟩

/-! ## Diamond cuts -/

private theorem executeDiamondCut_eq_some {E : Env} {i : Init} {s s' : St} :
    executeDiamondCut E i s = some s' ↔
      runInit E i s = some s' ∧
        ¬ (s'.secondProofSystemRequired = true ∧
            E.proofMode s'.verifier 0 ≠ some MULTI_PROOF_TYPE) := by
  unfold executeDiamondCut
  cases hr : runInit E i s with
  | none => simp
  | some t =>
    dsimp only
    rw [ite_none_eq_some_iff]
    constructor
    · rintro ⟨hc, h⟩
      cases h
      exact ⟨rfl, hc⟩
    · rintro ⟨h, hc⟩
      cases h
      exact ⟨hc, rfl⟩

/-- The re-check of `Admin.sol:121-126`, whatever the init. -/
private theorem cut_recheck {E : Env} {i : Init} {s s' : St}
    (h : executeDiamondCut E i s = some s') (hf : s'.secondProofSystemRequired = true) :
    E.proofMode s'.verifier 0 = some MULTI_PROOF_TYPE := by
  obtain ⟨-, hc⟩ := executeDiamondCut_eq_some.mp h
  by_contra hn
  exact hc ⟨hf, hn⟩

private theorem genuineInit_eq_some {E : Env} {g : GenuineInit} {s s' : St}
    (h : genuineInit E g s = some s') : ∃ v, s' = { s with verifier := v } := by
  rcases g with ⟨_ | v⟩
  · have h' : some s = some s' := h
    cases h'
    exact ⟨s.verifier, rfl⟩
  · have h' : (if v = 0 then none
        else if s.secondProofSystemRequired = true ∧ E.proofMode v 0 ≠ some MULTI_PROOF_TYPE
          then none
        else some { s with verifier := v }) = some s' := h
    rw [ite_none_eq_some_iff, ite_none_eq_some_iff] at h'
    obtain ⟨-, -, h'⟩ := h'
    cases h'
    exact ⟨v, rfl⟩

/-- A cut with no init or a genuine init writes at most the verifier, and leaves a flagged
diamond with a verifier that reports multi-proof mode for the zero mask. -/
private theorem cut_nonArb {E : Env} {i : Init} {s s' : St} (hi : i.isArbitrary = false)
    (h : executeDiamondCut E i s = some s') :
    ∃ v, s' = { s with verifier := v } ∧
      (s'.secondProofSystemRequired = true → E.proofMode s'.verifier 0 = some MULTI_PROOF_TYPE) := by
  obtain ⟨hr, -⟩ := executeDiamondCut_eq_some.mp h
  have key : ∃ v, s' = { s with verifier := v } := by
    cases i with
    | none =>
      have hr' : some s = some s' := hr
      cases hr'
      exact ⟨s.verifier, rfl⟩
    | genuine g => exact genuineInit_eq_some hr
    | arbitrary f => exact absurd hi (by simp [Init.isArbitrary])
  obtain ⟨v, hv⟩ := key
  exact ⟨v, hv, cut_recheck h⟩

/-! ## One step, inverted -/

private theorem step_inv (rule : St → Bool → Address) {E : Env} {c : Address} {call : Call}
    {s s' : St} (hb : call.isBreakGlass = false) (h : stepWith rule E c call s = some s') :
    (∃ en, call = .setProofSystemStatus .zisk en ∧ c = rule s en ∧
        s' = { s with disabledProofSystems := newMask s.disabledProofSystems .zisk en }) ∨
    (call = .permanentlyRequireSecondProofSystem ∧ c = s.admin ∧ s.settlementLayer = 0 ∧
        s.secondProofSystemRequired = false ∧
        E.proofMode s.verifier s.disabledProofSystems = some MULTI_PROOF_TYPE ∧
        s' = { s with secondProofSystemRequired := true }) ∨
    (call.isSetStatus = false ∧
        s'.secondProofSystemRequired = s.secondProofSystemRequired ∧
        s'.disabledProofSystems = s.disabledProofSystems ∧
        (s'.verifier = s.verifier ∨
          (s'.secondProofSystemRequired = true →
            E.proofMode s'.verifier 0 = some MULTI_PROOF_TYPE))) := by
  cases call with
  | setPendingAdmin a =>
    rw [step_setPendingAdmin, ite_none_eq_some_iff] at h
    obtain ⟨-, h⟩ := h
    cases h
    exact Or.inr (Or.inr ⟨rfl, rfl, rfl, Or.inl rfl⟩)
  | acceptAdmin =>
    rw [step_acceptAdmin, ite_none_eq_some_iff] at h
    obtain ⟨-, h⟩ := h
    cases h
    exact Or.inr (Or.inr ⟨rfl, rfl, rfl, Or.inl rfl⟩)
  | setProofSystemStatus p en =>
    rw [step_setStatus, ite_none_eq_some_iff, ite_none_eq_some_iff] at h
    obtain ⟨hc, hp, h⟩ := h
    have hp' : p = .zisk := not_not.mp hp
    subst hp'
    cases h
    exact Or.inl ⟨en, rfl, not_not.mp hc, rfl⟩
  | permanentlyRequireSecondProofSystem =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := require_iff.mp h
    exact Or.inr (Or.inl ⟨rfl, h1, h2, h3, h4, h5⟩)
  | upgradeChainFromVersion i =>
    rw [step_upgrade] at h
    obtain ⟨v, hv, hm⟩ := cut_nonArb hb h
    subst hv
    exact Or.inr (Or.inr ⟨rfl, rfl, rfl, Or.inr hm⟩)
  | executeUpgrade i =>
    rw [step_execute, ite_none_eq_some_iff] at h
    obtain ⟨v, hv, hm⟩ := cut_nonArb hb h.2
    subst hv
    exact Or.inr (Or.inr ⟨rfl, rfl, rfl, Or.inr hm⟩)
  | genesisUpgrade i =>
    rw [step_genesis, ite_none_eq_some_iff] at h
    obtain ⟨v, hv, hm⟩ := cut_nonArb hb h.2
    subst hv
    exact Or.inr (Or.inr ⟨rfl, rfl, rfl, Or.inr hm⟩)
  | adminOther e =>
    have h' : some s = some s' := h
    cases h'
    exact Or.inr (Or.inr ⟨rfl, rfl, rfl, Or.inl rfl⟩)
  | migratorSetsSettlementLayer sl =>
    have h' : some { s with settlementLayer := sl } = some s' := h
    cases h'
    exact Or.inr (Or.inr ⟨rfl, rfl, rfl, Or.inl rfl⟩)
  | bridgehubOwnerChanged o =>
    have h' : some { s with bridgehubOwner := o } = some s' := h
    cases h'
    exact Or.inr (Or.inr ⟨rfl, rfl, rfl, Or.inl rfl⟩)
  | otherFacet =>
    have h' : some s = some s' := h
    cases h'
    exact Or.inr (Or.inr ⟨rfl, rfl, rfl, Or.inl rfl⟩)

/-! ## Runs -/

private theorem reach_inv {rule : St → Bool → Address} {E : Env}
    {ok : St → Address → Call → Prop} {P : St → Prop}
    (hstep : ∀ s c call s', ok s c call → stepWith rule E c call s = some s' → P s → P s')
    {s s' : St} (h : ReachWith rule E ok s s') : P s → P s' := by
  induction h with
  | refl s => exact id
  | step c call hok hs _ ih => exact fun hp => ih (hstep _ _ _ _ hok hs hp)

/-- A one-call run. -/
private theorem reach_one {rule : St → Bool → Address} {E : Env}
    {ok : St → Address → Call → Prop} {s s' : St} (c : Address) (call : Call)
    (hok : ok s c call) (h : stepWith rule E c call s = some s') : ReachWith rule E ok s s' :=
  ReachWith.step c call hok h (ReachWith.refl s')

/-! ## (a) The flag is one-way -/

theorem PermanentlyRequireExact : Properties.PermanentlyRequireExact :=
  fun _ _ _ _ => require_iff (rule := callerRule)

theorem PermanentlyRequireOnce : Properties.PermanentlyRequireOnce := by
  intro E c s hf
  cases h : step E c .permanentlyRequireSecondProofSystem s with
  | none => rfl
  | some s' =>
    exact absurd (((require_iff (rule := callerRule)).mp h).2.2.1.symm.trans hf)
      Bool.false_ne_true

theorem FlagMonotoneStep : Properties.FlagMonotoneStep := by
  intro E c call s s' hb h hf
  rcases step_inv callerRule hb h with ⟨en, -, -, hs⟩ | ⟨-, -, -, -, -, hs⟩ | ⟨-, hfl, -, -⟩
  · subst hs; exact hf
  · subst hs; rfl
  · exact hfl.trans hf

theorem FlagMonotone : Properties.FlagMonotone := by
  intro E s s' hr
  exact reach_inv (P := fun x => x.secondProofSystemRequired = true)
    (fun s c call s' hok hs hp => FlagMonotoneStep E c call s s' hok hs hp) hr

theorem FlagSetOnlyByAdmin : Properties.FlagSetOnlyByAdmin := by
  intro E c call s s' hb h h0 h1
  rcases step_inv callerRule hb h with
    ⟨en, -, -, hs⟩ | ⟨hcall, hc, hsl, -, hpm, -⟩ | ⟨-, hfl, -, -⟩
  · subst hs
    exact absurd (h0.symm.trans h1) Bool.false_ne_true
  · exact ⟨hcall, hc, hsl, hpm⟩
  · exact absurd (h0.symm.trans (hfl.symm.trans h1)) Bool.false_ne_true

theorem CtmCutEntryPointsAreCtmOnly : Properties.CtmCutEntryPointsAreCtmOnly := by
  intro E c i s s'
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : stepWith callerRule E c (.executeUpgrade i) s = some s' := h
    rw [step_execute, ite_none_eq_some_iff] at h'
    exact not_not.mp h'.1
  · have h' : stepWith callerRule E c (.genesisUpgrade i) s = some s' := h
    rw [step_genesis, ite_none_eq_some_iff] at h'
    exact not_not.mp h'.1

theorem DiamondCutRecheck : Properties.DiamondCutRecheck := by
  intro E c i s s' h hf
  rcases h with h | h | h
  · have h' : stepWith callerRule E c (.upgradeChainFromVersion i) s = some s' := h
    rw [step_upgrade] at h'
    exact cut_recheck h' hf
  · have h' : stepWith callerRule E c (.executeUpgrade i) s = some s' := h
    rw [step_execute, ite_none_eq_some_iff] at h'
    exact cut_recheck h'.2 hf
  · have h' : stepWith callerRule E c (.genesisUpgrade i) s = some s' := h
    rw [step_genesis, ite_none_eq_some_iff] at h'
    exact cut_recheck h'.2 hf

private theorem clearFlag_step :
    step multiProofEnv w1.chainTypeManager (.executeUpgrade clearFlagInit) w1 = some w0 := by
  decide

theorem InitClearsFlag : Properties.InitClearsFlag := by
  refine ⟨⟨w0, clearFlag_step, rfl, rfl⟩, ?_, ?_⟩
  · intro H
    exact absurd (H multiProofEnv _ _ w1 w0 clearFlag_step rfl) (by decide)
  · intro H
    have hr : Reach multiProofEnv AnyCall w1 w0 :=
      reach_one (s := w1) (s' := w0) w1.chainTypeManager (.executeUpgrade clearFlagInit)
        trivial clearFlag_step
    exact absurd (H multiProofEnv w1 w0 hr rfl) (by decide)

/-- `w0` to `w1`: the admin sets the flag. -/
private theorem w0_require_w1 :
    step multiProofEnv w0.admin .permanentlyRequireSecondProofSystem w0 = some w1 := by
  decide

/-- `w1` to `w2`: the admin's genuine upgrade to the verifier at `11`. -/
private theorem w1_upgrade_w2 :
    step multiProofEnv w1.admin (.upgradeChainFromVersion (.genuine ⟨some 11⟩)) w1 = some w2 := by
  decide

/-- `w1` to `w3`: the Bridgehub owner's emergency ZiSK-off. -/
private theorem w1_ownerOff_w3 :
    step multiProofEnv w1.bridgehubOwner (.setProofSystemStatus .zisk false) w1 = some w3 := by
  decide

/-- `w3` to `w1`: the admin's ZiSK-on. -/
private theorem w3_adminOn_w1 :
    step multiProofEnv w3.admin (.setProofSystemStatus .zisk true) w3 = some w1 := by
  decide

/-- `w0` to `w4`: the unflagged diamond's admin switches ZiSK off. -/
private theorem w0_adminOff_w4 :
    step multiProofEnv w0.admin (.setProofSystemStatus .zisk false) w0 = some w4 := by
  decide

/-- `w4` to `w0`: and back on. -/
private theorem w4_adminOn_w0 :
    step multiProofEnv w4.admin (.setProofSystemStatus .zisk true) w4 = some w0 := by
  decide

theorem PermanentlyRequireGuardsWitness : Properties.PermanentlyRequireGuardsWitness := by
  refine ⟨w0_require_w1, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem FlagMonotoneRunWitness : Properties.FlagMonotoneRunWitness := by
  refine ⟨w1_ownerOff_w3, w3_adminOn_w1, w1_upgrade_w2, ?_, rfl, rfl, by decide⟩
  exact ReachWith.step (s' := w3) w1.bridgehubOwner (.setProofSystemStatus .zisk false) rfl
    w1_ownerOff_w3
    (ReachWith.step (s' := w1) w3.admin (.setProofSystemStatus .zisk true) rfl w3_adminOn_w1
      (reach_one (s := w1) (s' := w2) w1.admin (.upgradeChainFromVersion (.genuine ⟨some 11⟩))
        rfl w1_upgrade_w2))

theorem VerifierChecksWitness : Properties.VerifierChecksWitness := by
  refine ⟨w1_upgrade_w2, rfl, by decide, by decide, by decide, by decide⟩

/-! ## (b) The caller rule -/

theorem ZiskOffAuthorityExact : Properties.ZiskOffAuthorityExact := by
  intro E c enabled s
  have key : ∀ c', (∃ s', step E c' (.setProofSystemStatus .zisk enabled) s = some s') ↔
      c' = callerRule s enabled := by
    intro c'
    constructor
    · rintro ⟨s', h⟩
      exact ((setStatus_zisk_iff (rule := callerRule)).mp h).1
    · intro hc
      exact ⟨_, (setStatus_zisk_iff (rule := callerRule)).mpr ⟨hc, rfl⟩⟩
  have rule_eq : callerRule s enabled =
      if enabled = false ∧ s.secondProofSystemRequired = true
      then s.bridgehubOwner else s.admin := by
    cases enabled <;> cases hf : s.secondProofSystemRequired <;> simp [callerRule, hf]
  refine ⟨?_, fun hne => ⟨?_, ?_⟩, ?_⟩
  · rw [key c, rule_eq]
  · rw [key, rule_eq]
    by_cases h : enabled = false ∧ s.secondProofSystemRequired = true
    · rw [ite_eq_left h]
      exact ⟨fun _ => h, fun _ => rfl⟩
    · rw [ite_eq_right h]
      exact ⟨fun h' => absurd h'.symm hne, fun h' => absurd h' h⟩
  · rw [key, rule_eq]
    by_cases h : enabled = false ∧ s.secondProofSystemRequired = true
    · rw [ite_eq_left h]
      exact ⟨fun h' => absurd h' hne, fun h' => absurd h h'⟩
    · rw [ite_eq_right h]
      exact ⟨fun _ => h, fun _ => rfl⟩
  · intro p hp
    show stepWith callerRule E c (.setProofSystemStatus p enabled) s = none
    rw [step_setStatus]
    by_cases hc : c ≠ callerRule s enabled
    · rw [ite_eq_left hc]
    · rw [ite_eq_right hc, ite_eq_left hp]

theorem SetProofSystemStatusEffect : Properties.SetProofSystemStatusEffect := by
  intro E c p enabled s s' h
  have h' : stepWith callerRule E c (.setProofSystemStatus p enabled) s = some s' := h
  rw [step_setStatus, ite_none_eq_some_iff, ite_none_eq_some_iff] at h'
  obtain ⟨-, hp, h'⟩ := h'
  have hp' : p = .zisk := not_not.mp hp
  subst hp'
  cases h'
  refine ⟨rfl, rfl, ?_, ?_, newMask_other _ _⟩
  · intro he
    subst he
    exact mask_enable_zisk _
  · intro he
    subst he
    exact mask_disable_zisk _

theorem MaskWrittenOnlyBySetStatus : Properties.MaskWrittenOnlyBySetStatus := by
  intro E c call s s' hb h hne
  rcases step_inv callerRule hb h with ⟨en, hcall, -, -⟩ | ⟨-, -, -, -, -, hs⟩ | ⟨-, -, hm, -⟩
  · exact ⟨en, hcall⟩
  · subst hs
    exact absurd rfl hne
  · exact absurd hm hne

private theorem nonZisk_step (E : Env) (k : UInt8) :
    ∀ s c call s', NoBreakGlass s c call → stepWith callerRule E c call s = some s' →
      s.disabledProofSystems &&& ~~~ziskBit = k → s'.disabledProofSystems &&& ~~~ziskBit = k := by
  intro s c call s' hb h hp
  rcases step_inv callerRule hb h with ⟨en, -, -, hs⟩ | ⟨-, -, -, -, -, hs⟩ | ⟨-, -, hm, -⟩
  · subst hs
    exact (newMask_other _ _).trans hp
  · subst hs
    exact hp
  · rw [hm]
    exact hp

theorem NonZiskBitsFrozen : Properties.NonZiskBitsFrozen := by
  intro E s s' hr
  have heq : s'.disabledProofSystems &&& ~~~ziskBit = s.disabledProofSystems &&& ~~~ziskBit :=
    reach_inv (P := fun x => x.disabledProofSystems &&& ~~~ziskBit =
        s.disabledProofSystems &&& ~~~ziskBit)
      (nonZisk_step E _) hr rfl
  refine ⟨heq, fun h0 => ?_⟩
  rw [airbender_via_other, heq, ← airbender_via_other]
  exact h0

theorem OwnerDisablesOnFlagged : Properties.OwnerDisablesOnFlagged := by
  intro E s hf
  refine ⟨{ s with disabledProofSystems := newMask s.disabledProofSystems .zisk false }, ?_,
    mask_disable_zisk _, hf⟩
  exact (setStatus_zisk_iff (rule := callerRule)).mpr ⟨(callerRule_false_flag hf).symm, rfl⟩

private theorem w3_eq :
    w3 = { w1 with disabledProofSystems := newMask w1.disabledProofSystems .zisk false } := by
  decide

private theorem flagged_w3 : FlaggedZiskOff w3 := flagged_iff.mpr ⟨rfl, by decide⟩

theorem AdminOnlyRuleLetsAdminDrop : Properties.AdminOnlyRuleLetsAdminDrop := by
  have hstep : stepWith adminOnlyRule multiProofEnv w1.admin
      (.setProofSystemStatus .zisk false) w1 = some w3 :=
    setStatus_zisk_iff.mpr ⟨rfl, w3_eq⟩
  refine ⟨by decide, rfl, by decide, hstep, flagged_w3, ?_, ?_⟩
  · exact reach_one (s := w1) (s' := w3) w1.admin (.setProofSystemStatus .zisk false)
      (And.intro (And.intro rfl (fun _ => by decide)) (fun h => nomatch h)) hstep
  · show stepWith callerRule multiProofEnv w1.admin (.setProofSystemStatus .zisk false) w1 = none
    rw [step_setStatus]
    exact ite_eq_left (by decide)

theorem CallerRuleWitness : Properties.CallerRuleWitness := by
  refine ⟨by decide, w1_ownerOff_w3, by decide, by decide, by decide, w0_adminOff_w4, by decide,
    by decide, by decide⟩

theorem NonZiskBitsWitness : Properties.NonZiskBitsWitness := by
  have h1 : step multiProofEnv w6.bridgehubOwner (.setProofSystemStatus .zisk false) w6 =
      some { w6 with disabledProofSystems := 5 } := by
    decide
  have h2 : step multiProofEnv w6.admin (.setProofSystemStatus .zisk true)
      { w6 with disabledProofSystems := 5 } = some w6 := by
    decide
  refine ⟨by decide, h1, h2, ?_, ?_, by decide, by decide⟩
  · exact reach_one w6.bridgehubOwner (.setProofSystemStatus .zisk false) rfl h1
  · exact reach_one w6.admin (.setProofSystemStatus .zisk true) rfl h2

/-! ## (c) The chain admin cannot drop the second proof system -/

theorem ZiskOffOnFlaggedIsOwners : Properties.ZiskOffOnFlaggedIsOwners := by
  intro E c call s s' hb h hf hon hoff
  rcases step_inv callerRule hb h with ⟨en, hcall, hc, hs⟩ | ⟨-, -, -, h0, -, -⟩ | ⟨-, -, hm, -⟩
  · subst hs
    cases en
    · exact ⟨hcall, hc.trans (callerRule_false_flag hf)⟩
    · exact absurd (mask_enable_zisk _) hoff
  · exact absurd (h0.symm.trans hf) Bool.false_ne_true
  · have hon' : ziskOn s' := by
      unfold ziskOn
      rw [hm]
      exact hon
    exact absurd hon' hoff

private theorem adminSide_step (E : Env) :
    ∀ s c call s', AdminSide s c call → stepWith callerRule E c call s = some s' →
      (s.secondProofSystemRequired = true ∧ ziskOn s) →
      (s'.secondProofSystemRequired = true ∧ ziskOn s') := by
  intro s c call s' hok h hP
  obtain ⟨hb, hns⟩ := hok
  obtain ⟨hf, hon⟩ := hP
  rcases step_inv callerRule hb h with ⟨en, hcall, hc, hs⟩ | ⟨-, -, -, h0, -, -⟩ | ⟨-, hfl, hm, -⟩
  · subst hs
    subst hcall
    have hcne := hns rfl
    cases en
    · exact absurd (hc.trans (callerRule_false_flag hf)) hcne
    · exact ⟨hf, mask_enable_zisk _⟩
  · exact absurd (h0.symm.trans hf) Bool.false_ne_true
  · refine ⟨hfl.trans hf, ?_⟩
    unfold ziskOn
    rw [hm]
    exact hon

theorem AdminCannotDropSecondProof : Properties.AdminCannotDropSecondProof := by
  intro E s s' hr hf hon
  exact reach_inv (P := fun x => x.secondProofSystemRequired = true ∧ ziskOn x)
    (adminSide_step E) hr ⟨hf, hon⟩

private theorem adminSideHonest_step (E : Env) :
    ∀ s c call s', AdminSideHonest E s c call → stepWith callerRule E c call s = some s' →
      ¬ FlaggedZiskOff s → ¬ FlaggedZiskOff s' := by
  intro s c call s' hok h hP hbad
  obtain ⟨hside, hhon⟩ := hok
  obtain ⟨hb, hns⟩ := hside
  obtain ⟨hf', hoff'⟩ := hbad
  rcases step_inv callerRule hb h with
    ⟨en, hcall, hc, hs⟩ | ⟨hcall, -, -, -, hpm, hs⟩ | ⟨-, hfl, hm, -⟩
  · subst hs
    subst hcall
    have hcne := hns rfl
    cases en
    · exact hcne (hc.trans (callerRule_false_flag hf'))
    · exact hoff' (mask_enable_zisk _)
  · subst hs
    exact hoff' (hhon hcall _ hpm)
  · refine hP (flagged_iff.mpr ⟨hfl.symm.trans hf', ?_⟩)
    unfold ziskOff
    rw [← hm]
    exact hoff'

theorem AdminNeverReachesFlaggedZiskOff : Properties.AdminNeverReachesFlaggedZiskOff := by
  intro E s s' hr
  exact reach_inv (P := fun x => ¬ FlaggedZiskOff x) (adminSideHonest_step E) hr

private theorem gate_step (E : Env) :
    ∀ s c call s', AdminSide s c call → stepWith callerRule E c call s = some s' →
      (InteropSecondProofGate E s ∧ s.disabledProofSystems = 0) →
      (InteropSecondProofGate E s' ∧ s'.disabledProofSystems = 0) := by
  intro s c call s' hok h hP
  obtain ⟨hb, hns⟩ := hok
  obtain ⟨hg, hz⟩ := hP
  obtain ⟨hf, hpm⟩ := hg
  have hpm0 : E.proofMode s.verifier 0 = some MULTI_PROOF_TYPE := by
    rw [hz] at hpm
    exact hpm
  rcases step_inv callerRule hb h with ⟨en, hcall, hc, hs⟩ | ⟨-, -, -, h0, -, -⟩ | ⟨-, hfl, hm, hv⟩
  · subst hs
    subst hcall
    have hcne := hns rfl
    cases en
    · exact absurd (hc.trans (callerRule_false_flag hf)) hcne
    · have hnm : newMask s.disabledProofSystems .zisk true = 0 := by
        rw [hz]
        decide
      refine ⟨gate_iff.mpr ⟨hf, ?_⟩, hnm⟩
      show E.proofMode s.verifier (newMask s.disabledProofSystems .zisk true) =
        some MULTI_PROOF_TYPE
      rw [hnm]
      exact hpm0
  · exact absurd (h0.symm.trans hf) Bool.false_ne_true
  · have hz' : s'.disabledProofSystems = 0 := hm.trans hz
    have hf' : s'.secondProofSystemRequired = true := hfl.trans hf
    refine ⟨gate_iff.mpr ⟨hf', ?_⟩, hz'⟩
    rw [hz']
    rcases hv with hv | hv
    · rw [hv]
      exact hpm0
    · exact hv hf'

theorem InteropGatePersists : Properties.InteropGatePersists := by
  intro E s s' hr hg hz
  exact reach_inv (P := fun x => InteropSecondProofGate E x ∧ x.disabledProofSystems = 0)
    (gate_step E) hr ⟨hg, hz⟩

private theorem gate_multiProof_iff (s : St) :
    InteropSecondProofGate multiProofEnv s ↔
      (s.secondProofSystemRequired = true ∧ s.disabledProofSystems = 0) := by
  constructor
  · rintro ⟨hf, hpm⟩
    exact ⟨hf, (multiProof_iff _).mp hpm⟩
  · rintro ⟨hf, hz⟩
    exact gate_iff.mpr ⟨hf, (multiProof_iff _).mpr hz⟩

private theorem gate_not_ziskOff (s : St) (hoff : ziskOff s) :
    ¬ InteropSecondProofGate multiProofEnv s := by
  intro hg
  have hz : s.disabledProofSystems = 0 := ((gate_multiProof_iff s).mp hg).2
  have hon : s.disabledProofSystems &&& ziskBit = 0 := by
    rw [hz]
    decide
  exact hoff hon

theorem InteropGatePersistsMultiProof : Properties.InteropGatePersistsMultiProof := by
  refine ⟨gate_multiProof_iff, gate_not_ziskOff, ?_⟩
  intro s s' hr hg
  exact (InteropGatePersists multiProofEnv s s' hr hg ((gate_multiProof_iff s).mp hg).2).1

theorem LyingVerifierFlagsWithZiskOff : Properties.LyingVerifierFlagsWithZiskOff := by
  refine ⟨?_, ?_, ⟨{ w4 with secondProofSystemRequired := true }, ?_, ?_⟩, w0_adminOff_w4,
    by decide⟩
  · rintro ⟨hf, -⟩
    exact absurd hf (by decide)
  · intro H
    have h4 : ziskBit &&& ziskBit = 0 := H ziskBit rfl
    exact absurd h4 (by decide)
  · have h1 : stepWith callerRule lyingEnv w0.admin (.setProofSystemStatus .zisk false) w0 =
        some w4 :=
      setStatus_zisk_iff.mpr ⟨by decide, by decide⟩
    have h2 : stepWith callerRule lyingEnv w4.admin .permanentlyRequireSecondProofSystem w4 =
        some { w4 with secondProofSystemRequired := true } :=
      require_iff.mpr ⟨rfl, rfl, rfl, rfl, rfl⟩
    exact ReachWith.step (s := w0) (s' := w4) w0.admin (.setProofSystemStatus .zisk false)
      (And.intro rfl (fun _ => by decide)) h1
      (reach_one (s := w4) w4.admin .permanentlyRequireSecondProofSystem
        (And.intro rfl (fun h => absurd h (by decide))) h2)
  · exact flagged_iff.mpr ⟨rfl, by decide⟩

private theorem ziskOffInit_step :
    step multiProofEnv w1.chainTypeManager (.executeUpgrade ziskOffInit) w1 = some w3 := by
  decide

theorem BreakGlassDropsSecondProof : Properties.BreakGlassDropsSecondProof := by
  refine ⟨rfl, by decide, ziskOffInit_step, flagged_w3, ?_, ?_⟩
  · exact reach_one (s := w1) (s' := w3) w1.chainTypeManager (.executeUpgrade ziskOffInit)
      (fun h => absurd h (by decide)) ziskOffInit_step
  · intro hr
    exact absurd (AdminCannotDropSecondProof multiProofEnv w1 w3 hr rfl (by decide)).2
      (by decide)

theorem InteropGateNeedsZeroMask : Properties.InteropGateNeedsZeroMask := by
  have hstep : step mixedEnv w3.admin (.upgradeChainFromVersion (.genuine ⟨some 11⟩)) w3 =
      some { w3 with verifier := 11 } := by
    decide
  refine ⟨gate_iff.mpr ⟨rfl, by decide⟩, by decide, { w3 with verifier := 11 }, hstep, ?_, ?_⟩
  · exact reach_one w3.admin (.upgradeChainFromVersion (.genuine ⟨some 11⟩))
      (And.intro rfl (fun h => absurd h (by decide))) hstep
  · intro hg
    exact absurd ((gate_iff.mp hg).2) (by decide)

/-- `w1` to `w5`: an admin handover to `4`, the Bridgehub owner becoming `5`, and the new
admin's genuine upgrade to the verifier at `11`, under `AdminSide`. -/
private theorem adminSideRun_w1_w5 : Reach multiProofEnv AdminSide w1 w5 := by
  have h1 : step multiProofEnv w1.admin (.setPendingAdmin 4) w1 =
      some { w1 with pendingAdmin := 4 } := by
    decide
  have h2 : step multiProofEnv 4 .acceptAdmin { w1 with pendingAdmin := 4 } =
      some { w1 with admin := 4 } := by
    decide
  have h3 : step multiProofEnv w1.bridgehubOwner (.bridgehubOwnerChanged 5)
      { w1 with admin := 4 } = some { w1 with admin := 4, bridgehubOwner := 5 } := by
    decide
  have h4 : step multiProofEnv 4 (.upgradeChainFromVersion (.genuine ⟨some 11⟩))
      { w1 with admin := 4, bridgehubOwner := 5 } = some w5 := by
    decide
  exact ReachWith.step w1.admin (.setPendingAdmin 4)
    (And.intro rfl (fun h => absurd h (by decide))) h1
    (ReachWith.step 4 .acceptAdmin (And.intro rfl (fun h => absurd h (by decide))) h2
      (ReachWith.step w1.bridgehubOwner (.bridgehubOwnerChanged 5)
        (And.intro rfl (fun h => absurd h (by decide))) h3
        (reach_one 4 (.upgradeChainFromVersion (.genuine ⟨some 11⟩))
          (And.intro rfl (fun h => absurd h (by decide))) h4)))

theorem AdminSideRunWitness : Properties.AdminSideRunWitness := by
  refine ⟨gate_iff.mpr ⟨rfl, by decide⟩, rfl, by decide, adminSideRun_w1_w5, by decide, by decide,
    by decide, rfl, by decide, gate_iff.mpr ⟨rfl, by decide⟩, by decide, ?_⟩
  exact ⟨{ w5 with disabledProofSystems := ziskBit }, by decide⟩

theorem HonestRunWitness : Properties.HonestRunWitness := by
  refine ⟨?_, by decide, ?_, ?_, rfl, by decide⟩
  · rintro ⟨hf, -⟩
    exact absurd hf (by decide)
  · exact reach_one w0.admin (.setProofSystemStatus .zisk false)
      (And.intro (And.intro rfl (fun _ => by decide)) (fun h => nomatch h)) w0_adminOff_w4
  · exact ReachWith.step (s' := w0) w4.admin (.setProofSystemStatus .zisk true)
      (And.intro (And.intro rfl (fun _ => by decide)) (fun h => nomatch h)) w4_adminOn_w0
      (ReachWith.step (s' := w1) w0.admin .permanentlyRequireSecondProofSystem
        (And.intro (And.intro rfl (fun h => absurd h (by decide)))
          (fun _ => multiProofEnv_reportsZisk _))
        w0_require_w1
        (reach_one (s := w1) (s' := w2) w1.admin (.upgradeChainFromVersion (.genuine ⟨some 11⟩))
          (And.intro (And.intro rfl (fun h => absurd h (by decide))) (fun h => nomatch h))
          w1_upgrade_w2))

/-! ## (d) Re-enabling is the chain admin's -/

theorem ReenableIsAdmins : Properties.ReenableIsAdmins := by
  intro E c p s s' h
  have h' : stepWith callerRule E c (.setProofSystemStatus p true) s = some s' := h
  rw [step_setStatus, ite_none_eq_some_iff] at h'
  exact (not_not.mp h'.1).trans (callerRule_true s)

theorem BridgehubOwnerCannotReenable : Properties.BridgehubOwnerCannotReenable := by
  intro E p s hne
  show stepWith callerRule E s.bridgehubOwner (.setProofSystemStatus p true) s = none
  rw [step_setStatus, callerRule_true]
  exact ite_eq_left hne

theorem AdminReenables : Properties.AdminReenables := by
  intro E s
  exact ⟨{ s with disabledProofSystems := newMask s.disabledProofSystems .zisk true },
    (setStatus_zisk_iff (rule := callerRule)).mpr ⟨(callerRule_true s).symm, rfl⟩,
    mask_enable_zisk _, rfl⟩

private theorem ownerSide_step (E : Env) :
    ∀ s c call s', OwnerSide s c call → stepWith callerRule E c call s = some s' →
      ziskOff s → ziskOff s' := by
  intro s c call s' hok h hP
  obtain ⟨hb, hns⟩ := hok
  rcases step_inv callerRule hb h with ⟨en, hcall, hc, hs⟩ | ⟨-, -, -, -, -, hs⟩ | ⟨-, -, hm, -⟩
  · subst hs
    subst hcall
    have hcne := hns rfl
    cases en
    · exact mask_disable_zisk _
    · exact absurd (hc.trans (callerRule_true s)) hcne
  · subst hs
    exact hP
  · unfold ziskOff
    rw [hm]
    exact hP

theorem ZiskStaysOffWithoutAdmin : Properties.ZiskStaysOffWithoutAdmin := by
  intro E s s' hr
  exact reach_inv (P := fun x => ziskOff x) (ownerSide_step E) hr

theorem BreakGlassReenables : Properties.BreakGlassReenables := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem OwnerSideRunWitness : Properties.OwnerSideRunWitness := by
  have h1 : step multiProofEnv w3.admin (.upgradeChainFromVersion (.genuine ⟨some 11⟩)) w3 =
      some { w3 with verifier := 11 } := by
    decide
  have h2 : step multiProofEnv w3.bridgehubOwner (.setProofSystemStatus .zisk false)
      { w3 with verifier := 11 } = some { w3 with verifier := 11 } := by
    decide
  have h3 : step multiProofEnv w3.bridgehubOwner (.bridgehubOwnerChanged 5)
      { w3 with verifier := 11 } = some { w3 with verifier := 11, bridgehubOwner := 5 } := by
    decide
  have h4 : step multiProofEnv 5 (.setProofSystemStatus .zisk false)
      { w3 with verifier := 11, bridgehubOwner := 5 } =
      some { w3 with verifier := 11, bridgehubOwner := 5 } := by
    decide
  refine ⟨by decide, ?_, by decide, by decide, by decide, w3_adminOn_w1⟩
  exact ReachWith.step w3.admin (.upgradeChainFromVersion (.genuine ⟨some 11⟩))
    (And.intro rfl (fun h => absurd h (by decide))) h1
    (ReachWith.step w3.bridgehubOwner (.setProofSystemStatus .zisk false)
      (And.intro rfl (fun _ => by decide)) h2
      (ReachWith.step w3.bridgehubOwner (.bridgehubOwnerChanged 5)
        (And.intro rfl (fun h => absurd h (by decide))) h3
        (reach_one 5 (.setProofSystemStatus .zisk false)
          (And.intro rfl (fun _ => by decide)) h4)))

/-! ## (e) The genuine verifier -/

theorem MultiProofVerifierReportsZisk : Properties.MultiProofVerifierReportsZisk :=
  ⟨multiProofEnv_reportsZisk, multiProof_iff⟩

/-! ## (f) Verifier answers that change between calls -/

private theorem reachEnvs_inv {ok : Env → St → Address → Call → Prop} {P : St → Prop}
    (hstep : ∀ E s c call s', ok E s c call → stepWith callerRule E c call s = some s' →
      P s → P s')
    {s s' : St} (h : ReachEnvs ok s s') : P s → P s' := by
  induction h with
  | refl s => exact id
  | step E c call hok hs _ ih => exact fun hp => ih (hstep _ _ _ _ _ hok hs hp)

/-- A one-call run of `ReachEnvs`. -/
private theorem reachEnvs_one {ok : Env → St → Address → Call → Prop} {s s' : St} (E : Env)
    (c : Address) (call : Call) (hok : ok E s c call)
    (h : stepWith callerRule E c call s = some s') : ReachEnvs ok s s' :=
  ReachEnvs.step E c call hok h (ReachEnvs.refl s')

theorem ReachEnvsExtendsReach : Properties.ReachEnvsExtendsReach := by
  intro E ok s s' h
  induction h with
  | refl s => exact ReachEnvs.refl s
  | step c call hok hs _ ih => exact ReachEnvs.step E c call hok hs ih

theorem FlagMonotoneAnyVerifiers : Properties.FlagMonotoneAnyVerifiers := by
  intro s s' hr
  refine ⟨reachEnvs_inv (P := fun x => x.secondProofSystemRequired = true)
    (fun E s c call s' hok hs hp => FlagMonotoneStep E c call s s' hok hs hp) hr, ?_⟩
  exact reachEnvs_inv (P := fun x => x.disabledProofSystems &&& ~~~ziskBit =
      s.disabledProofSystems &&& ~~~ziskBit)
    (fun E => nonZisk_step E _) hr rfl

theorem AdminCannotDropSecondProofAnyVerifiers :
    Properties.AdminCannotDropSecondProofAnyVerifiers := by
  intro s s' hr hf hon
  exact reachEnvs_inv (P := fun x => x.secondProofSystemRequired = true ∧ ziskOn x)
    (fun E => adminSide_step E) hr ⟨hf, hon⟩

theorem AdminNeverReachesFlaggedZiskOffAnyVerifiers :
    Properties.AdminNeverReachesFlaggedZiskOffAnyVerifiers := by
  intro s s' hr
  exact reachEnvs_inv (P := fun x => ¬ FlaggedZiskOff x) (fun E => adminSideHonest_step E) hr

theorem ZiskStaysOffWithoutAdminAnyVerifiers :
    Properties.ZiskStaysOffWithoutAdminAnyVerifiers := by
  intro s s' hr
  exact reachEnvs_inv (P := fun x => ziskOff x) (fun E => ownerSide_step E) hr

theorem AnyVerifiersRunWitness : Properties.AnyVerifiersRunWitness := by
  -- `AdminSideHonest` from `w0`: lying answers, then genuine ones, then `airbenderAt12Env`.
  have a1 : stepWith callerRule lyingEnv w0.admin (.setProofSystemStatus .zisk false) w0 =
      some w4 := by
    decide
  have a2 : stepWith callerRule lyingEnv w4.admin (.setProofSystemStatus .zisk true) w4 =
      some w0 := by
    decide
  have a4 : stepWith callerRule airbenderAt12Env w1.admin
      (.upgradeChainFromVersion (.genuine ⟨some 11⟩)) w1 = some w2 := by
    decide
  have hHonest : ReachEnvs AdminSideHonest w0 w2 :=
    ReachEnvs.step lyingEnv w0.admin (.setProofSystemStatus .zisk false)
      (And.intro (And.intro rfl (fun _ => by decide)) (fun h => nomatch h)) a1
      (ReachEnvs.step lyingEnv w4.admin (.setProofSystemStatus .zisk true)
        (And.intro (And.intro rfl (fun _ => by decide)) (fun h => nomatch h)) a2
        (ReachEnvs.step multiProofEnv w0.admin .permanentlyRequireSecondProofSystem
          (And.intro (And.intro rfl (fun h => absurd h (by decide)))
            (fun _ => multiProofEnv_reportsZisk _))
          w0_require_w1
          (reachEnvs_one airbenderAt12Env w1.admin (.upgradeChainFromVersion (.genuine ⟨some 11⟩))
            (And.intro (And.intro rfl (fun h => absurd h (by decide))) (fun h => nomatch h))
            a4)))
  -- `AdminSide` from `w1` and `OwnerSide` from `w3`: genuine answers, then lying ones.
  have b2 : stepWith callerRule lyingEnv w1.admin
      (.upgradeChainFromVersion (.genuine ⟨some 12⟩)) w2 = some { w1 with verifier := 12 } := by
    decide
  have hAdmin : ReachEnvs (fun _ => AdminSide) w1 { w1 with verifier := 12 } :=
    ReachEnvs.step multiProofEnv w1.admin (.upgradeChainFromVersion (.genuine ⟨some 11⟩))
      (And.intro rfl (fun h => absurd h (by decide))) w1_upgrade_w2
      (reachEnvs_one lyingEnv w1.admin (.upgradeChainFromVersion (.genuine ⟨some 12⟩))
        (And.intro rfl (fun h => absurd h (by decide))) b2)
  have c1 : stepWith callerRule multiProofEnv w3.admin
      (.upgradeChainFromVersion (.genuine ⟨some 11⟩)) w3 = some { w3 with verifier := 11 } := by
    decide
  have c2 : stepWith callerRule lyingEnv w3.admin
      (.upgradeChainFromVersion (.genuine ⟨some 12⟩)) { w3 with verifier := 11 } =
      some { w3 with verifier := 12 } := by
    decide
  have hOwner : ReachEnvs (fun _ => OwnerSide) w3 { w3 with verifier := 12 } :=
    ReachEnvs.step multiProofEnv w3.admin (.upgradeChainFromVersion (.genuine ⟨some 11⟩))
      (And.intro rfl (fun h => absurd h (by decide))) c1
      (reachEnvs_one lyingEnv w3.admin (.upgradeChainFromVersion (.genuine ⟨some 12⟩))
        (And.intro rfl (fun h => absurd h (by decide))) c2)
  -- No break-glass cut from `w6`: a lying answer, then a genuine one.
  have d1 : stepWith callerRule lyingEnv w6.bridgehubOwner (.setProofSystemStatus .zisk false)
      w6 = some { w6 with disabledProofSystems := 5 } := by
    decide
  have d2 : stepWith callerRule multiProofEnv w6.admin
      (.upgradeChainFromVersion (.genuine ⟨some 11⟩)) { w6 with disabledProofSystems := 5 } =
      some { w6 with disabledProofSystems := 5, verifier := 11 } := by
    decide
  have hNoBreak : ReachEnvs (fun _ => NoBreakGlass) w6
      { w6 with disabledProofSystems := 5, verifier := 11 } :=
    ReachEnvs.step lyingEnv w6.bridgehubOwner (.setProofSystemStatus .zisk false) rfl d1
      (reachEnvs_one multiProofEnv w6.admin (.upgradeChainFromVersion (.genuine ⟨some 11⟩))
        rfl d2)
  refine ⟨?_, hHonest, rfl, by decide, hAdmin, ?_, by decide, hOwner, by decide, hNoBreak⟩
  · rintro ⟨hf, -⟩
    exact absurd hf (by decide)
  · intro H
    have h4 : ziskBit &&& ziskBit = 0 := H ziskBit rfl
    exact absurd h4 (by decide)

end Contracts.SecondProofSystem.FlagAuthorityV35
