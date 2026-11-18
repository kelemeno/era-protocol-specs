import EraSpec.Contracts.SecondProofSystem.Properties.MigrationV35

/-!
# Proofs: the second-proof-system requirement of one chain, its two diamonds and migration

The run-level results are inductions over `Run` with a one-step lemma each:

* `dstep_frame`: a call on one diamond other than a break-glass cut never writes
  `settlementLayer`, never clears either flag, changes the verifier only to one that reports
  multi-proof mode for the empty mask while the flag is set, and changes the mask only by an
  admitted `setProofSystemStatus(Zisk, _)`;
* `src_step`: with migrations disabled, a chain settling on L1 still does after any modelled
  call but a break-glass cut, and its L1 diamond changes only as `dstep_frame` allows;
* `kept_step`: every modelled call but a break-glass cut preserves `PermanentRollupKept`.

`dstep_frame` re-derives, in this topic's model, one-diamond facts that `FlagAuthorityV35`
states in its own model (the folder README lists them); nothing here imports that topic.

The witnesses are evaluated: `exec` runs a list of calls, checking the run predicate before
each, and `exec_run` turns a successful execution into a `Run`.
-/

namespace Contracts.SecondProofSystem.MigrationV35

/-! ## Bits of the mask -/

/-- A mask is its ZiSK bit and the rest. -/
private lemma mask_split (m : UInt8) : m = (m &&& ~~~ziskBit) ||| (m &&& ziskBit) := by
  apply UInt8.toBitVec_inj.1
  simp only [UInt8.toBitVec_or, UInt8.toBitVec_and, UInt8.toBitVec_not]
  rw [← BitVec.and_or_distrib_left, BitVec.or_comm, BitVec.or_not_self, BitVec.and_allOnes]

/-- Turning ZiSK on clears the ZiSK bit. -/
private lemma zisk_on_clears (m : UInt8) : (m &&& ~~~ziskBit) &&& ziskBit = 0 := by
  rw [UInt8.and_assoc]; simp

theorem MultiProofModeIffNothingDisabled : Properties.MultiProofModeIffNothingDisabled := by
  intro m
  constructor
  · intro h
    unfold multiProofGetProofMode at h
    by_cases h1 : m &&& ~~~ziskBit = 0
    · by_cases h2 : m &&& ziskBit = 0
      · rw [mask_split m, h1, h2]; rfl
      · simp [h1, h2, PLONK_TYPE, MULTI_PROOF_TYPE] at h
    · simp [h1] at h
  · rintro rfl; decide

/-! ## One diamond -/

/-- The re-check after a cut either keeps the diamond or reverts. -/
private lemma postCutCheck_some {E : Env} {d d' : Diamond} (h : postCutCheck E d = some d') :
    d' = d ∧ (d.secondProofSystemRequired = true →
      E.proofMode d.verifier 0 = some MULTI_PROOF_TYPE) := by
  unfold postCutCheck at h
  split_ifs at h with hc
  cases h
  refine ⟨rfl, fun hf => ?_⟩
  by_contra hne
  exact hc ⟨hf, hne⟩

/-- What a call on one diamond, other than a break-glass cut, can change. -/
private lemma dstep_frame {E : Env} {o c : Address} {dc : DCall} {d d' : Diamond}
    (hbg : ∀ f, dc ≠ .breakGlassCut f) (h : dstep E o c dc d = some d') :
    d'.settlementLayer = d.settlementLayer ∧
    (d.secondProofSystemRequired = true → d'.secondProofSystemRequired = true) ∧
    (d.isPermanentRollup = true → d'.isPermanentRollup = true) ∧
    (d'.verifier = d.verifier ∨
      (d'.secondProofSystemRequired = true →
        E.proofMode d'.verifier 0 = some MULTI_PROOF_TYPE)) ∧
    (d'.disabledProofSystems = d.disabledProofSystems ∨
      ∃ en, dc = .setProofSystemStatus .zisk en ∧ c = authorized o d en ∧
        d'.disabledProofSystems = newMask d.disabledProofSystems .zisk en) := by
  cases dc with
  | setPendingAdmin a =>
    simp only [dstep] at h
    split_ifs at h
    cases h
    exact ⟨rfl, id, id, Or.inl rfl, Or.inl rfl⟩
  | acceptAdmin =>
    simp only [dstep] at h
    split_ifs at h
    cases h
    exact ⟨rfl, id, id, Or.inl rfl, Or.inl rfl⟩
  | setProofSystemStatus p en =>
    simp only [dstep] at h
    split_ifs at h with h1 h2
    cases h
    have hp : p = .zisk := by simpa using h2
    subst hp
    refine ⟨rfl, id, id, Or.inl rfl, Or.inr ⟨en, rfl, ?_, rfl⟩⟩
    simpa using h1
  | permanentlyRequireSecondProofSystem =>
    simp only [dstep] at h
    split_ifs at h
    cases h
    exact ⟨rfl, fun _ => rfl, id, Or.inl rfl, Or.inl rfl⟩
  | makePermanentRollup =>
    simp only [dstep] at h
    split_ifs at h
    cases h
    exact ⟨rfl, id, fun _ => rfl, Or.inl rfl, Or.inl rfl⟩
  | upgrade v =>
    cases v with
    | none =>
      obtain ⟨rfl, _⟩ := postCutCheck_some h
      exact ⟨rfl, id, id, Or.inl rfl, Or.inl rfl⟩
    | some v =>
      simp only [dstep] at h
      split_ifs at h
      obtain ⟨rfl, hck⟩ := postCutCheck_some h
      exact ⟨rfl, id, id, Or.inr hck, Or.inl rfl⟩
  | breakGlassCut f => exact absurd rfl (hbg f)

/-- A call other than a break-glass cut, as `Call.isBreakGlass` says it. -/
private lemma not_breakGlass {L : Layer} {dc : DCall}
    (h : (Call.diamond L dc).isBreakGlass = false) : ∀ f, dc ≠ .breakGlassCut f := by
  intro f hf
  subst hf
  simp [Call.isBreakGlass] at h

/-- A successful call on the L1 diamond. -/
private lemma step_l1 {cfg : Cfg} {E : Env} {c : Address} {dc : DCall} {s s' : Sys}
    (h : step cfg E c (.diamond .l1 dc) s = some s') :
    ∃ d', dstep E s.l1BridgehubOwner c dc s.l1 = some d' ∧ s' = { s with l1 := d' } := by
  simp only [step, Option.map_eq_some_iff] at h
  obtain ⟨d', hd, rfl⟩ := h
  exact ⟨d', hd, rfl⟩

/-- A successful call on the gateway diamond. -/
private lemma step_gw {cfg : Cfg} {E : Env} {c : Address} {dc : DCall} {s s' : Sys}
    (h : step cfg E c (.diamond .gw dc) s = some s') :
    ∃ d d', s.gw = some d ∧ dstep E s.gwBridgehubOwner c dc d = some d' ∧
      s' = { s with gw := some d' } := by
  simp only [step] at h
  cases hg : s.gw with
  | none => rw [hg] at h; simp at h
  | some d =>
    rw [hg] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨d', hd, rfl⟩ := h
    exact ⟨d, d', rfl, hd, rfl⟩

/-! ## The source: migrations disabled -/

theorem MigrationBanRefusesEveryMigration : Properties.MigrationBanRefusesEveryMigration := by
  intro cfg E c call s hcfg hmig
  cases call <;> simp_all [Call.isMigration, step]

/-- One step with migrations disabled, from a chain that settles on L1. -/
private lemma src_step {cfg : Cfg} {E : Env} {c : Address} {call : Call} {s s' : Sys}
    (hcfg : cfg.migrationsEnabled = false) (hbg : call.isBreakGlass = false)
    (h : step cfg E c call s = some s') (hset : SettlesOnL1 s) :
    SettlesOnL1 s' ∧
    (s.l1.secondProofSystemRequired = true → s'.l1.secondProofSystemRequired = true) ∧
    (s'.l1.verifier = s.l1.verifier ∨
      (s'.l1.secondProofSystemRequired = true →
        E.proofMode s'.l1.verifier 0 = some MULTI_PROOF_TYPE)) ∧
    (s'.l1.disabledProofSystems = s.l1.disabledProofSystems ∨
      ∃ en, call = .diamond .l1 (.setProofSystemStatus .zisk en) ∧
        c = authorized s.l1BridgehubOwner s.l1 en ∧
        s'.l1.disabledProofSystems = newMask s.l1.disabledProofSystems .zisk en) ∧
    (s.interopEnabled = true → s'.interopEnabled = true) := by
  obtain ⟨hacc, hgw⟩ := hset
  cases call with
  | diamond L dc =>
    have hbg' := not_breakGlass hbg
    cases L with
    | l1 =>
      obtain ⟨d', hd, rfl⟩ := step_l1 h
      obtain ⟨hsl, hf, -, hv, hm⟩ := dstep_frame hbg' hd
      refine ⟨⟨?_, hgw⟩, hf, hv, ?_, id⟩
      · show d'.settlementLayer = 0
        rw [hsl]; exact hacc
      · rcases hm with hm | ⟨en, rfl, hc, hm⟩
        · exact Or.inl hm
        · exact Or.inr ⟨en, rfl, hc, hm⟩
    | gw =>
      obtain ⟨d, d', hg, hd, rfl⟩ := step_gw h
      obtain ⟨hsl, -⟩ := dstep_frame hbg' hd
      refine ⟨⟨hacc, ?_⟩, id, Or.inl rfl, Or.inl rfl, id⟩
      intro e he
      cases he
      have := hgw d hg
      unfold Diamond.accepts at this ⊢
      rwa [hsl]
  | bridgeBurnToGateway sl na p => simp [step, hcfg] at h
  | bridgeMintOnGateway f => simp [step, hcfg] at h
  | bridgeBurnToL1 na p => simp [step, hcfg] at h
  | bridgeMintOnL1 f => simp [step, hcfg] at h
  | bridgeConfirmFailure f =>
    exfalso
    unfold Diamond.accepts at hacc
    simp [step, hacc] at h
  | enableInterop req =>
    simp only [step] at h
    split_ifs at h
    cases h
    exact ⟨⟨hacc, hgw⟩, id, Or.inl rfl, Or.inl rfl, fun _ => rfl⟩
  | transferBridgehubOwnership L o =>
    cases L <;> simp only [step] at h <;> split_ifs at h <;> cases h <;>
      exact ⟨⟨hacc, hgw⟩, id, Or.inl rfl, Or.inl rfl, id⟩

/-- A ZiSK-off on L1 needs the owner of L1's Bridgehub once the flag is set. -/
private lemma l1_ziskOff_needs_owner {cfg : Cfg} {E : Env} {c : Address} {p : ProofSystem}
    {s s'' : Sys} (hf : s.l1.secondProofSystemRequired = true)
    (h : step cfg E c (.diamond .l1 (.setProofSystemStatus p false)) s = some s'') :
    c = s.l1BridgehubOwner := by
  obtain ⟨d', hd, -⟩ := step_l1 h
  simp only [dstep] at hd
  split_ifs at hd with h1
  have : c = authorized s.l1BridgehubOwner s.l1 false := by simpa using h1
  simpa [authorized, hf] using this

theorem RequirementPermanentWhileMigrationsDisabled :
    Properties.RequirementPermanentWhileMigrationsDisabled := by
  intro cfg E s s' tr hcfg hrun hset hf
  -- invariant: settles on L1, flag set, verifier multi-proof at `0` if it was at the start
  have key : ∀ {t t' : Sys} {tr : List (Address × Call)}, Run cfg E Tame t tr t' →
      SettlesOnL1 t → t.l1.secondProofSystemRequired = true →
      (E.proofMode s.l1.verifier 0 = some MULTI_PROOF_TYPE →
        E.proofMode t.l1.verifier 0 = some MULTI_PROOF_TYPE) →
      SettlesOnL1 t' ∧ t'.l1.secondProofSystemRequired = true ∧
      (E.proofMode s.l1.verifier 0 = some MULTI_PROOF_TYPE →
        E.proofMode t'.l1.verifier 0 = some MULTI_PROOF_TYPE) := by
    intro t t' tr hr
    induction hr with
    | nil t => exact fun h1 h2 h3 => ⟨h1, h2, h3⟩
    | @cons t t₁ t₂ c call tr hok hstep _ ih =>
      intro h1 h2 h3
      obtain ⟨hs1, hf1, hv1, -, -⟩ := src_step hcfg hok hstep h1
      have hf1 := hf1 h2
      refine ih hs1 hf1 fun hq => ?_
      rcases hv1 with hv | hv
      · rw [hv]; exact h3 hq
      · exact hv hf1
  obtain ⟨hs', hf', hv'⟩ := key hrun hset hf id
  exact ⟨hs', hf', hv', fun c p s'' h => l1_ziskOff_needs_owner hf' h⟩

/-- `setProofSystemStatus(Zisk, _)` keeps a mask that is `0` or the ZiSK bit in that set. -/
private lemma newMask_zero_or_zisk {m : UInt8} (hm : m = 0 ∨ m = ziskBit) (en : Bool) :
    newMask m .zisk en = 0 ∨ newMask m .zisk en = ziskBit := by
  rcases hm with rfl | rfl <;> cases en <;> decide

theorem MultiProofOrZiskOffWhileMigrationsDisabled :
    Properties.MultiProofOrZiskOffWhileMigrationsDisabled := by
  intro cfg E s s' tr hcfg hrun
  induction hrun with
  | nil t =>
    intro _ _ hm hv
    rcases hm with hm | hm
    · exact Or.inl ⟨hm, by rw [hm]; exact hv⟩
    · exact Or.inr hm
  | @cons t t₁ t₂ c call tr hok hstep _ ih =>
    intro hset hf hm hv
    obtain ⟨hs1, hf1, hv1, hm1, -⟩ := src_step hcfg hok hstep hset
    have hf1 := hf1 hf
    refine ih hs1 hf1 ?_ ?_
    · rcases hm1 with hm1 | ⟨en, -, -, hm1⟩
      · rw [hm1]; exact hm
      · rw [hm1]; exact newMask_zero_or_zisk hm en
    · rcases hv1 with hv1 | hv1
      · rw [hv1]; exact hv
      · exact hv1 hf1

/-- `NoL1OwnerZiskOff` allows no break-glass cut. -/
private lemma noL1OwnerZiskOff_tame {s : Sys} {c : Address} {call : Call}
    (h : NoL1OwnerZiskOff s c call) : call.isBreakGlass = false := h.1

theorem ZiskStaysOnWithoutTheBridgehubOwner :
    Properties.ZiskStaysOnWithoutTheBridgehubOwner := by
  intro cfg E s s' tr hcfg hrun
  induction hrun with
  | nil t => exact fun _ _ h => h
  | @cons t t₁ t₂ c call tr hok hstep _ ih =>
    intro hset hf hz
    obtain ⟨hs1, hf1, -, hm1, -⟩ := src_step hcfg (noL1OwnerZiskOff_tame hok) hstep hset
    refine ih hs1 (hf1 hf) ?_
    rcases hm1 with hm | ⟨en, rfl, hc, hm⟩
    · unfold ziskOff at hz ⊢; rwa [hm]
    · cases en with
      | false =>
        exfalso
        have hown : c = t.l1BridgehubOwner := by simpa [authorized, hf] using hc
        exact hok.2 rfl hown
      | true =>
        unfold ziskOff
        rw [hm]
        simp only [newMask]
        exact not_not.mpr (zisk_on_clears _)

theorem MultiProofKeptWhileMigrationsDisabled :
    Properties.MultiProofKeptWhileMigrationsDisabled := by
  intro cfg E s s' tr hcfg hrun
  induction hrun with
  | nil t => exact fun h1 h2 h3 h4 => ⟨h1, h2, h3, by rw [h3]; exact h4, id⟩
  | @cons t t₁ t₂ c call tr hok hstep _ ih =>
    intro hset hf hm0 hv0
    obtain ⟨hs1, hf1, hv1, hm1, hi1⟩ := src_step hcfg (noL1OwnerZiskOff_tame hok) hstep hset
    have hf1 := hf1 hf
    have hm1' : t₁.l1.disabledProofSystems = 0 := by
      rcases hm1 with hm | ⟨en, rfl, hc, hm⟩
      · rw [hm, hm0]
      · cases en with
        | false =>
          exfalso
          have hown : c = t.l1BridgehubOwner := by simpa [authorized, hf] using hc
          exact hok.2 rfl hown
        | true =>
          rw [hm, hm0]
          simp [newMask]
    have hv1' : E.proofMode t₁.l1.verifier 0 = some MULTI_PROOF_TYPE := by
      rcases hv1 with hv | hv
      · rw [hv]; exact hv0
      · exact hv hf1
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih hs1 hf1 hm1' hv1'
    exact ⟨h1, h2, h3, h4, fun hi => h5 (hi1 hi)⟩

/-! ## Enabling interop -/

theorem EnableInteropSucceedsIff : Properties.EnableInteropSucceedsIff := by
  intro cfg E c req s s'
  simp only [step]
  constructor
  · intro h
    split_ifs at h with h1 h2 h3
    cases h
    refine ⟨by simpa using h1, by simpa using h2, fun hr => ?_, rfl⟩
    by_contra hn
    exact h3 ⟨hr, hn⟩
  · rintro ⟨rfl, h2, h3, rfl⟩
    rw [ite_eq_right (not_not.mpr rfl), ite_eq_right (by simp [h2]), ite_eq_right]
    rintro ⟨hr, hn⟩
    exact hn (h3 hr)

theorem EnabledChainStaysMultiProof : Properties.EnabledChainStaysMultiProof := by
  intro cfg E c s s₁ s' tr hcfg hset hcode hen hrun
  obtain ⟨-, -, hreq, rfl⟩ := (EnableInteropSucceedsIff cfg E c true s s₁).1 hen
  obtain ⟨hf, hmode⟩ := hreq rfl
  rw [hcode] at hmode
  have hm0 : s.l1.disabledProofSystems = 0 := (MultiProofModeIffNothingDisabled _).1 hmode
  have hv0 : E.proofMode s.l1.verifier 0 = some MULTI_PROOF_TYPE := by
    rw [hcode]; decide
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    MultiProofKeptWhileMigrationsDisabled cfg E _ s' tr hcfg hrun hset hf hm0 hv0
  exact ⟨h5 rfl, h1, h2, h3, h4⟩

/-! ## The migration path -/

theorem AwayDiamondCannotRequire : Properties.AwayDiamondCannotRequire := by
  intro E owner c d hd
  unfold Diamond.accepts at hd
  simp only [dstep]
  split_ifs <;> rfl

theorem PermanentRollupCarried : Properties.PermanentRollupCarried := by
  refine ⟨fun payload c d h => ?_, fun c d d' h => ?_, fun c d hd hc => ?_⟩
  · unfold prepareChainCommitment at h
    split_ifs at h
    cases h
    rfl
  · unfold forwardedBridgeMint at h
    split_ifs at h
    cases h
    rfl
  · unfold forwardedBridgeMint
    rw [ite_eq_left ⟨hd, hc⟩]

/-- What a successful `prepareChainCommitment` carries. -/
private lemma prepare_isPermanentRollup {payload c : Commitment} {d : Diamond}
    (h : prepareChainCommitment payload d = some c) : c.isPermanentRollup = d.isPermanentRollup :=
  PermanentRollupCarried.1 payload c d h

/-- What a successful `forwardedBridgeMint` leaves. -/
private lemma mint_facts {c : Commitment} {d d' : Diamond} (h : forwardedBridgeMint c d = some d') :
    d'.isPermanentRollup = c.isPermanentRollup ∧ d'.settlementLayer = 0 := by
  unfold forwardedBridgeMint at h
  split_ifs at h
  cases h
  exact ⟨rfl, rfl⟩

/-- Every call but a break-glass cut preserves `PermanentRollupKept`. -/
private lemma kept_step {cfg : Cfg} {E : Env} {c : Address} {call : Call} {s s' : Sys}
    (hbg : call.isBreakGlass = false) (h : step cfg E c call s = some s')
    (hk : PermanentRollupKept s) : PermanentRollupKept s' := by
  obtain ⟨k1, k2, k3⟩ := hk
  cases call with
  | diamond L dc =>
    have hbg' := not_breakGlass hbg
    cases L with
    | l1 =>
      obtain ⟨d', hd, rfl⟩ := step_l1 h
      obtain ⟨hsl, -, hp, -⟩ := dstep_frame hbg' hd
      refine ⟨fun ha => hp (k1 ?_), k2, fun f hf => ?_⟩
      · unfold Diamond.accepts at ha ⊢; rwa [← hsl]
      · obtain ⟨hw, hd'⟩ := k3 f hf
        exact ⟨hw, fun hdir => hp (hd' hdir)⟩
    | gw =>
      obtain ⟨d, d', hg, hd, rfl⟩ := step_gw h
      obtain ⟨hsl, -, hp, -⟩ := dstep_frame hbg' hd
      refine ⟨k1, fun e he ha => ?_, k3⟩
      cases he
      refine hp (k2 d hg ?_)
      unfold Diamond.accepts at ha ⊢; rwa [← hsl]
  | bridgeBurnToGateway sl na p =>
    simp only [step] at h
    split_ifs at h with h1 h2 h3 h4 h5 h6
    cases hw : prepareChainCommitment p s.l1 with
    | none => rw [hw] at h; simp at h
    | some w =>
      rw [hw] at h
      cases h
      have hacc : s.l1.accepts := by unfold Diamond.accepts; simpa using h3
      have hpr := k1 hacc
      refine ⟨fun ha => ?_, k2, fun f hf => ?_⟩
      · exfalso
        exact h4 ha
      · simp only [List.mem_cons] at hf
        rcases hf with rfl | hf
        · exact ⟨by rw [prepare_isPermanentRollup hw]; exact hpr, fun _ => hpr⟩
        · exact k3 f hf
  | bridgeMintOnGateway f =>
    cases hg : s.gw with
    | none =>
      simp only [step, hg] at h
      split_ifs at h with h1 h2 h3
      have hw := (k3 f (by simpa using h2)).1
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨d', hd, rfl⟩ := h
      refine ⟨k1, fun e he _ => ?_, fun g hg' => k3 g (List.mem_of_mem_erase hg')⟩
      cases he
      rw [(mint_facts hd).1, hw]
    | some d =>
      simp only [step, hg] at h
      split_ifs at h with h1 h2 h3
      have hw := (k3 f (by simpa using h2)).1
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨d', hd, rfl⟩ := h
      refine ⟨k1, fun e he _ => ?_, fun g hg' => k3 g (List.mem_of_mem_erase hg')⟩
      cases he
      rw [(mint_facts hd).1, hw]
  | bridgeBurnToL1 na p =>
    cases hg : s.gw with
    | none => simp [step, hg] at h
    | some d =>
      simp only [step, hg] at h
      split_ifs at h with h1 h2 h3 h4 h5
      cases hw : prepareChainCommitment p d with
      | none => rw [hw] at h; simp at h
      | some w =>
        rw [hw] at h
        cases h
        have hacc : d.accepts := by unfold Diamond.accepts; simpa using h3
        have hpr := k2 d hg hacc
        refine ⟨k1, fun e he _ => ?_, fun f hf => ?_⟩
        · cases he; exact hpr
        · simp only [List.mem_cons] at hf
          rcases hf with rfl | hf
          · exact ⟨by rw [prepare_isPermanentRollup hw]; exact hpr, fun hdir => by cases hdir⟩
          · exact k3 f hf
  | bridgeMintOnL1 f =>
    simp only [step] at h
    split_ifs at h with h1 h2 h3 h4
    have hfm : f ∈ s.inFlight := by simpa using h2
    have hw := (k3 f hfm).1
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨d', hd, rfl⟩ := h
    have hpr : d'.isPermanentRollup = true := by rw [(mint_facts hd).1, hw]
    exact ⟨fun _ => hpr, k2, fun g hg => ⟨(k3 g (List.mem_of_mem_erase hg)).1, fun _ => hpr⟩⟩
  | bridgeConfirmFailure f =>
    simp only [step] at h
    split_ifs at h with h1 h2 h3
    cases h
    have hfm : f ∈ s.inFlight := by simpa using h1
    have hdir : f.dir = .toGateway := by simpa using h2
    have hpr := (k3 f hfm).2 hdir
    exact ⟨fun _ => hpr, k2, fun g hg => ⟨(k3 g (List.mem_of_mem_erase hg)).1, fun _ => hpr⟩⟩
  | enableInterop req =>
    simp only [step] at h
    split_ifs at h
    cases h
    exact ⟨k1, k2, k3⟩
  | transferBridgehubOwnership L o =>
    cases L <;> simp only [step] at h <;> split_ifs at h <;> cases h <;> exact ⟨k1, k2, k3⟩

theorem PermanentRollupKeptAcrossMigration : Properties.PermanentRollupKeptAcrossMigration := by
  intro cfg E s s' tr hrun
  induction hrun with
  | nil t => exact id
  | cons hok hstep _ ih => exact fun hk => ih (kept_step hok hstep hk)

/-! ## Witnesses -/

/-- Run a list of calls, checking `ok` before each; `none` if a check or a call fails. -/
private def exec (cfg : Cfg) (E : Env) (ok : Sys → Address → Call → Prop)
    [∀ s c call, Decidable (ok s c call)] : Sys → List (Address × Call) → Option Sys
  | s, [] => some s
  | s, (c, call) :: tr =>
    if ok s c call then
      match step cfg E c call s with
      | none => none
      | some s' => exec cfg E ok s' tr
    else none

/-- A successful execution is a run. -/
private lemma exec_run {cfg : Cfg} {E : Env} {ok : Sys → Address → Call → Prop}
    [∀ s c call, Decidable (ok s c call)] :
    ∀ {s s' : Sys} {tr : List (Address × Call)}, exec cfg E ok s tr = some s' →
      Run cfg E ok s tr s'
  | s, s', [], h => by
    simp only [exec, Option.some.injEq] at h
    subst h
    exact .nil s
  | s, s', (c, call) :: tr, h => by
    simp only [exec] at h
    split_ifs at h with hok
    cases hst : step cfg E c call s with
    | none => rw [hst] at h; simp at h
    | some s₁ =>
      rw [hst] at h
      exact .cons hok hst (exec_run h)

/-- `w2` settles on L1. -/
private lemma w2_settles : SettlesOnL1 w2 := ⟨by decide, fun d h => by cases h⟩

/-- `w3` settles on L1. -/
private lemma w3_settles : SettlesOnL1 w3 := ⟨by decide, fun d h => by cases h⟩

theorem RequirementPermanentWitness : Properties.RequirementPermanentWitness := by
  refine ⟨exec_run (by decide), w3_settles, rfl, rfl, by decide,
    ⟨{ w3 with l1 := { w3.l1 with verifier := 12, disabledProofSystems := ziskBit } },
     { w3 with l1 := { w3.l1 with verifier := 12 } },
     exec_run (by decide), rfl, by decide, exec_run (by decide), rfl, by decide, rfl, by decide⟩,
    by decide, by decide, by decide, by decide⟩

theorem MultiProofKeptWitness : Properties.MultiProofKeptWitness := by
  refine ⟨exec_run (by decide), w2_settles, rfl, rfl, by decide, fun m => ?_, by decide,
    by decide, by decide, exec_run (by decide), rfl, rfl, rfl, by decide, by decide, by decide,
    by decide, by decide⟩
  show (if (10 : Address) = 20 then some PLONK_TYPE else multiProofGetProofMode m) = _
  rw [ite_eq_right (by decide)]

/-- A gateway diamond that forwards to L1 does not accept the chain's batches. -/
private lemma wDormant_away : ¬ wDormant.accepts := by decide

theorem ReturnedChainWitness : Properties.ReturnedChainWitness := by
  refine ⟨⟨by decide, fun d h => ?_⟩, rfl, wDormant_away, rfl, rfl, rfl, by decide,
    exec_run (by decide), ⟨by decide, fun d h => ?_⟩, rfl, by decide⟩
  · cases h; exact wDormant_away
  · cases h; decide

theorem AwayDiamondCannotRequireWitness : Properties.AwayDiamondCannotRequireWitness := by
  refine ⟨by decide, by decide, by decide⟩

/-- `wRollup` keeps `PermanentRollupKept`. -/
private lemma wRollup_kept : PermanentRollupKept wRollup :=
  ⟨fun _ => rfl, (fun d h => by cases h), (fun f hf => by cases hf)⟩

/-- `wRollupAway` keeps `PermanentRollupKept`. -/
private lemma wRollupAway_kept : PermanentRollupKept wRollupAway := by
  refine ⟨fun h => absurd h (by decide), fun d h _ => ?_, fun f hf => by cases hf⟩
  cases h
  rfl

/-- `wRollupHome` keeps `PermanentRollupKept`. -/
private lemma wRollupHome_kept : PermanentRollupKept wRollupHome := by
  refine ⟨fun _ => rfl, fun d h ha => ?_, fun f hf => by cases hf⟩
  cases h
  exact absurd ha (by decide)

theorem PermanentRollupKeptWitness : Properties.PermanentRollupKeptWitness :=
  ⟨by decide, rfl, by decide,
    exec_run (by decide), wRollup_kept, exec_run (by decide), wRollupAway_kept, by decide,
    ⟨_, rfl, by decide, rfl⟩, exec_run (by decide), wRollupHome_kept, by decide, rfl,
    ⟨_, rfl, by decide, rfl⟩, by decide⟩

end Contracts.SecondProofSystem.MigrationV35
