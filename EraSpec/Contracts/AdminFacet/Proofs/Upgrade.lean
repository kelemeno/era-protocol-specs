import EraSpec.Contracts.AdminFacet.Properties.Upgrade
import EraSpec.Contracts.AdminFacet.Proofs.Access

/-!
# Proofs: chain upgrades through the facet

Each `Properties.X` of `EraSpec.Contracts.AdminFacet.Properties.Upgrade` is proved as `X`.
-/

namespace Contracts.AdminFacet

/-! ## Unfolding lemmas -/

theorem executeDiamondCut_eq_some {K : Config} {e : Env} {τ : ℕ} {cut : Cut} {s s' : State} :
    executeDiamondCut K e τ cut s = some s' ↔
      K.runCut e τ cut s = some s' ∧
      (s'.secondProofSystemRequired = true →
        e.getProofMode s'.verifier 0 = ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE) := by
  unfold executeDiamondCut
  cases h : K.runCut e τ cut s with
  | none => simp
  | some s₁ =>
    simp only [req_eq_some, Option.some.injEq]
    constructor
    · rintro ⟨hp, rfl⟩; exact ⟨rfl, hp⟩
    · rintro ⟨rfl, hp⟩; exact ⟨hp, rfl⟩

theorem upgradeWithCut_eq_some {K : Config} {e : Env} {s s' : State} {c : Call} {v : ℕ}
    {cut : Cut} :
    upgradeWithCut K e s c v cut = some s' ↔
      s.protocolVersion = v ∧
      (c.sender ≠ s.admin ∧ c.sender ≠ s.chainTypeManager →
        e.upgradeTimestamp s.chainTypeManager v ≠ 0 ∧
        e.upgradeTimestamp s.chainTypeManager v ≤ c.time) ∧
      K.runCut e c.time cut s = some s' ∧
      (s'.secondProofSystemRequired = true →
        e.getProofMode s'.verifier 0 = ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE) ∧
      v < s'.protocolVersion := by
  unfold upgradeWithCut
  simp only [req_eq_some]
  cases h : executeDiamondCut K e c.time cut s with
  | none =>
    simp only [reduceCtorEq, and_false, false_iff, not_and]
    intro _ _ hr hp
    have := executeDiamondCut_eq_some.2 ⟨hr, hp⟩
    rw [h] at this; cases this
  | some s₁ =>
    obtain ⟨hr, hp⟩ := executeDiamondCut_eq_some.1 h
    simp only [req_eq_some, Option.some.injEq]
    constructor
    · rintro ⟨hv, hg, hlt, rfl⟩; exact ⟨hv, hg, hr, hp, hlt⟩
    · rintro ⟨hv, hg, hr', hp', hlt⟩
      rw [hr] at hr'; cases hr'
      exact ⟨hv, hg, hlt, rfl⟩

theorem genesisEffect_eq_some {e : Env} {s s' : State} (h : genesisEffect e s = some s') :
    s.upgradeTxHash = 0 ∧
      s' = { s with upgradeTxHash := e.genesisTxHash s.chainTypeManager s.protocolVersion } := by
  unfold genesisEffect at h
  simp only [req_eq_some, Option.some.injEq] at h
  exact ⟨h.2.2.1, h.2.2.2.2.symm⟩

/-- Under `GenuineGenesis`, a successful `genesisUpgrade` call needs a zero L2 upgrade hash, writes
the CTM's genesis hash, and keeps the version. -/
theorem genesis_call {K : Config} {e : Env} {s s' : State} {a : Address} {τ : ℕ}
    (hg : GenuineGenesis K) (h : call K e s ⟨a, τ, .genesisUpgrade⟩ = some s') :
    s.upgradeTxHash = 0 ∧
      s'.upgradeTxHash = e.genesisTxHash s.chainTypeManager s.protocolVersion ∧
      s'.protocolVersion = s.protocolVersion := by
  have h := call_exec h
  simp only [exec, req_eq_some] at h
  obtain ⟨_, h⟩ := h
  obtain ⟨hr, _⟩ := executeDiamondCut_eq_some.1 h
  obtain ⟨h0, rfl⟩ := genesisEffect_eq_some (hg e τ s s' hr)
  exact ⟨h0, rfl, rfl⟩

theorem upgrade_call {K : Config} {e : Env} {s s' : State} {a : Address} {τ : ℕ} {ch : Address}
    {v : ℕ} (h : call K e s ⟨a, τ, .upgradeChainFromVersion ch v⟩ = some s') :
    s.protocolVersion = v ∧ v < s'.protocolVersion := by
  have h := call_exec h
  simp only [exec, req_eq_some] at h
  obtain ⟨_, h⟩ := h
  cases hcut : e.upgradeCutForVersion s.chainTypeManager v with
  | none => simp [hcut] at h
  | some cut =>
    simp only [hcut] at h
    obtain ⟨hv, _, _, _, hlt⟩ := upgradeWithCut_eq_some.1 h
    exact ⟨hv, hlt⟩

theorem Label.runsCut_cases {l : Label} (h : l.runsCut = true) :
    l.isUpgrade = true ∨ l.isExecuteUpgrade = true ∨ l.isGenesis = true := by
  rcases l with ⟨a, τ, en⟩ | _ | _ <;>
    first
    | (cases en <;> simp_all [Label.runsCut, Entry.runsCut, Label.isUpgrade,
        Label.isExecuteUpgrade, Label.isGenesis])
    | simp_all [Label.runsCut]

/-! ## Properties -/

theorem upgrade_runs_exactly_the_committed_cut :
    Properties.UpgradeRunsExactlyTheCommittedCut := by
  intro K e s s' a τ ch v
  simp only [call, exec, req_eq_some]
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  cases hcut : e.upgradeCutForVersion s.chainTypeManager v with
  | none => simp
  | some cut =>
    simp only [Option.some.injEq, exists_eq_left', upgradeWithCut_eq_some]

theorem version_rises_along_runs : Properties.VersionRisesAlongRuns := by
  intro K w w' ls hg hr
  induction hr with
  | nil => intro _; simp
  | @cons w w₁ w₂ l ls hs _ ih =>
    intro hne
    have ih := ih (fun l' hl' => hne l' (List.mem_cons_of_mem _ hl'))
    have hl := hne l List.mem_cons_self
    -- the head step
    have key : w.st.protocolVersion + (if l.isUpgrade then 1 else 0) ≤ w₁.st.protocolVersion := by
      cases hs with
      | @call c s' hc =>
        rcases c with ⟨a, τ, en⟩
        cases hcut : en.runsCut
        · have := (exec_fixed (call_exec hc) hcut).2.1
          have hu : (Label.call ⟨a, τ, en⟩).isUpgrade = false := by
            cases en <;> simp_all [Entry.runsCut, Label.isUpgrade]
          simp [hu, this]
        · cases en <;> simp [Entry.runsCut] at hcut
          · obtain ⟨hv, hlt⟩ := upgrade_call hc
            simp [Label.isUpgrade]; omega
          · simp [Label.isExecuteUpgrade] at hl
          · have := (genesis_call hg hc).2.2
            simp [Label.isUpgrade, this]
      | env => simp [Label.isUpgrade]
      | foreign hf => simp [Label.isUpgrade, hf.protocolVersion]
    rw [List.countP_cons]
    omega

theorem genesis_runs_once : Properties.GenesisRunsOnce := by
  intro K w w₁ w₂ a τ ls hg hs hne hr hcut hfor
  have h1 : w₁.st.upgradeTxHash ≠ 0 := by
    cases hs with
    | call hc => rw [(genesis_call hg hc).2.1]; exact hne
  clear hs
  induction hr with
  | nil => intro l hl; cases hl
  | @cons w w₁ w₂ l ls hs _ ih =>
    have hl := hcut l List.mem_cons_self
    -- the head step is not a genesis upgrade, and keeps the hash nonzero
    have key : l.isGenesis = false ∧ w₁.st.upgradeTxHash ≠ 0 := by
      cases hs with
      | @call c s' hc =>
        rcases c with ⟨b, σ, en⟩
        cases hrc : en.runsCut
        · refine ⟨?_, ?_⟩
          · cases en <;> simp_all [Entry.runsCut, Label.isGenesis]
          · rw [(exec_fixed (call_exec hc) hrc).2.2.2.2]; exact h1
        · cases en <;> simp [Entry.runsCut] at hrc
          · simp [Label.isUpgrade] at hl
          · simp [Label.isExecuteUpgrade] at hl
          · exact absurd (genesis_call hg hc).1 h1
      | env => exact ⟨rfl, h1⟩
      | foreign hf => exact ⟨rfl, hfor _ List.mem_cons_self⟩
    intro l' hl'
    rcases List.mem_cons.1 hl' with rfl | hl'
    · exact key.1
    · exact ih (fun l hl => hcut l (List.mem_cons_of_mem _ hl))
        (fun s' hs' => hfor s' (List.mem_cons_of_mem _ hs')) key.2 l' hl'

/-! ## Witnesses and countermodels -/

/-- A deployment whose genesis address holds the genuine code and whose every other cut raises the
version by one. -/
def bumpConfig : Config where
  onL1 := true
  runCut := fun e _ cut s =>
    if cut = genesisCut (e.l1GenesisUpgrade s.chainTypeManager) then genesisEffect e s
    else some { s with protocolVersion := s.protocolVersion + 1 }

theorem bumpConfig_genuine : GenuineGenesis bumpConfig := by
  intro e τ s s' h; simpa [bumpConfig] using h

/-- The CTM `9` points genesis at `42` with transaction hash `77`, has a cut committed for version
`0`, and the notifier's timestamp is `10`. -/
def upEnv : Env :=
  { nullEnv with
    l1GenesisUpgrade := fun _ => 42
    genesisTxHash := fun _ _ => 77
    upgradeCutForVersion := fun _ v => if v = 0 then some ⟨[], 43, 0⟩ else none
    upgradeTimestamp := fun _ _ => 10 }

/-- After the CTM's genesis upgrade: the genesis transaction (hash `77`) is pending. -/
def up1 : State := { freshState with upgradeTxHash := 77 }
/-- After the Executor finalized it (`Executor.sol:209-210`). -/
def up2 : State := { up1 with upgradeTxHash := 0 }
/-- After the CTM made `7` a validator. -/
def up3 : State :=
  { up2 with validators := fun x => if x = 7 then true else up2.validators x }
/-- After the validator's upgrade from version `0`. -/
def up4 : State := { up3 with protocolVersion := 1 }

theorem genesis_from_fresh :
    call bumpConfig upEnv freshState ⟨9, 0, .genesisUpgrade⟩ = some up1 := by
  simp [call, exec, req, executeDiamondCut, bumpConfig, genesisEffect, upEnv, up1, freshState,
    genesisCut]

theorem upgrade_witness : Properties.UpgradeWitness := by
  refine ⟨bumpConfig, ⟨freshState, upEnv⟩, ⟨up4, upEnv⟩,
    [.call ⟨9, 0, .genesisUpgrade⟩, .foreign up2, .call ⟨9, 0, .setValidator 7 true⟩,
     .call ⟨7, 10, .upgradeChainFromVersion 0 0⟩], 7, 10, bumpConfig_genuine, ?_, ?_, ?_,
    by decide, by decide, rfl, rfl, rfl, rfl⟩
  · refine Run.cons (w₁ := ⟨up1, upEnv⟩) (Step.call genesis_from_fresh) ?_
    refine Run.cons (w₁ := ⟨up2, upEnv⟩) (Step.foreign ⟨rfl, fun h => h⟩) ?_
    refine Run.cons (w₁ := ⟨up3, upEnv⟩) (Step.call rfl) ?_
    refine Run.cons (Step.call ?_) (Run.nil _)
    simp [call, exec, req, upgradeWithCut, executeDiamondCut, bumpConfig, upEnv, up4, up3, up2,
      up1, freshState, genesisCut]
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inr (Or.inr rfl))

/-- `up1` after another facet committed batch `1` carrying the pending upgrade transaction. -/
def upCommitted : State := { up1 with totalBatchesCommitted := 1, upgradeBatchNumber := 1 }
/-- `upEnv` after the notifier's schedule moved to `20`. -/
def upEnv' : Env := { upEnv with upgradeTimestamp := fun _ _ => 20 }

theorem genesis_runs_once_witness : Properties.GenesisRunsOnceWitness := by
  refine ⟨bumpConfig, ⟨freshState, upEnv⟩, ⟨up1, upEnv⟩,
    ⟨{ upCommitted with validators := fun x => if x = 7 then true else upCommitted.validators x },
      upEnv'⟩, 9, 0,
    [.foreign upCommitted, .env upEnv', .call ⟨9, 0, .setValidator 7 true⟩],
    bumpConfig_genuine, Step.call genesis_from_fresh, by decide, ?_, ?_, ?_,
    ⟨⟨9, 0, .setValidator 7 true⟩, by simp⟩, ⟨upEnv', by simp⟩, ⟨upCommitted, by simp⟩⟩
  · refine Run.cons (Step.foreign ⟨rfl, fun h => h⟩) ?_
    refine Run.cons (Step.env _) ?_
    exact Run.cons (Step.call rfl) (Run.nil _)
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
  · intro s' hs'
    simp only [List.mem_cons, List.not_mem_nil, or_false, Label.foreign.injEq, reduceCtorEq,
      or_false] at hs'
    subst hs'; decide

/-- A deployment whose genesis address holds the genuine code and whose every other cut sets the
version to `0`. -/
def lowerConfig : Config where
  onL1 := true
  runCut := fun e _ cut s =>
    if cut = genesisCut (e.l1GenesisUpgrade s.chainTypeManager) then genesisEffect e s
    else some { s with protocolVersion := 0 }

theorem lowerConfig_genuine : GenuineGenesis lowerConfig := by
  intro e τ s s' h; simpa [lowerConfig] using h

theorem execute_upgrade_can_lower_version : Properties.ExecuteUpgradeCanLowerVersion := by
  refine ⟨lowerConfig, ⟨{ freshState with protocolVersion := 5 }, nullEnv⟩, ⟨freshState, nullEnv⟩,
    [.call ⟨9, 0, .executeUpgrade ⟨[], 1, 0⟩⟩], lowerConfig_genuine, ?_, by decide, by decide⟩
  refine Run.cons (Step.call ?_) (Run.nil _)
  simp [call, exec, req, executeDiamondCut, lowerConfig, genesisCut, freshState, nullEnv]

/-- An environment with a cut committed for version `0`. -/
def idEnv : Env := { nullEnv with upgradeCutForVersion := fun _ _ => some ⟨[], 1, 0⟩ }

theorem upgrade_post_check_is_load_bearing : Properties.UpgradePostCheckIsLoadBearing :=
  ⟨⟨true, fun _ _ _ s => some s⟩, idEnv, freshState, freshState, 0, 0, rfl, le_refl _, rfl⟩

theorem genesis_reruns_after_finalization : Properties.GenesisRerunsAfterFinalization := by
  refine ⟨bumpConfig, ⟨freshState, upEnv⟩, ⟨up1, upEnv⟩, ⟨up1, upEnv⟩, 9, 0,
    [.foreign freshState, .call ⟨9, 0, .genesisUpgrade⟩], bumpConfig_genuine,
    Step.call genesis_from_fresh, by decide, ?_, ?_, ⟨freshState, List.mem_cons_self, rfl⟩,
    ⟨.call ⟨9, 0, .genesisUpgrade⟩, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩⟩
  · refine Run.cons (w₁ := ⟨freshState, upEnv⟩) (Step.foreign ⟨rfl, fun h => h⟩) ?_
    exact Run.cons (Step.call genesis_from_fresh) (Run.nil _)
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> exact ⟨rfl, rfl⟩

/-! ## Certificates -/

theorem UpgradeRunsExactlyTheCommittedCut : Properties.UpgradeRunsExactlyTheCommittedCut :=
  upgrade_runs_exactly_the_committed_cut
theorem VersionRisesAlongRuns : Properties.VersionRisesAlongRuns :=
  version_rises_along_runs
theorem GenesisRunsOnce : Properties.GenesisRunsOnce :=
  genesis_runs_once
theorem UpgradeWitness : Properties.UpgradeWitness :=
  upgrade_witness
theorem GenesisRunsOnceWitness : Properties.GenesisRunsOnceWitness :=
  genesis_runs_once_witness
theorem ExecuteUpgradeCanLowerVersion : Properties.ExecuteUpgradeCanLowerVersion :=
  execute_upgrade_can_lower_version
theorem UpgradePostCheckIsLoadBearing : Properties.UpgradePostCheckIsLoadBearing :=
  upgrade_post_check_is_load_bearing
theorem GenesisRerunsAfterFinalization : Properties.GenesisRerunsAfterFinalization :=
  genesis_reruns_after_finalization

end Contracts.AdminFacet
