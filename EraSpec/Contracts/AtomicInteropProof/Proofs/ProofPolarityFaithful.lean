import EraSpec.Contracts.AtomicInteropProof.Properties.ProofPolarityFaithful

/-! # Proofs: proof polarity with the declared chain kept apart
(see `../Specs/ProofPolarityFaithful.lean`) -/

namespace AttackVectors.ProofPolarityFaithful

variable {Chain Value : Type}

/-! ## Reachable states -/

theorem pinnedReach_honest {srcOf : Value → Chain} {tree : Chain → Set Value}
    (h : PinnedReach srcOf tree) : HonestInsertion srcOf tree := by
  induction h with
  | genesis => intro c v hv; simp at hv
  | @append tree c v _ hsrc ih =>
    intro c' w hw
    rcases hw with hw | ⟨rfl, rfl⟩
    · exact ih c' w hw
    · exact hsrc

theorem upgradeReach_declared {srcOf decl : Value → Chain} {tree : Chain → Set Value}
    (h : UpgradeReach srcOf decl tree) : HonestInsertion srcOf tree ∧ DeclaredInsertion decl tree := by
  induction h with
  | genesis => exact ⟨fun c v hv => by simp at hv, fun c v hv => by simp at hv⟩
  | @append tree c v _ hsrc hdecl ih =>
    refine ⟨fun c' w hw => ?_, fun c' w hw => ?_⟩
    · rcases hw with hw | ⟨rfl, rfl⟩
      · exact ih.1 c' w hw
      · exact hsrc
    · rcases hw with hw | ⟨rfl, rfl⟩
      · exact ih.2 c' w hw
      · exact hdecl

/-! ## The gates -/

theorem checked_gates_exclusive {decl : Value → Chain} {tree : Chain → Set Value}
    {legs : List Value} {pc : Value → Chain} (hfin : FlowFinalizedChecked decl tree legs pc) :
    ¬ FlowRefunded decl tree legs := by
  rintro ⟨v, hv, c, hc, habs⟩
  obtain ⟨hpc, hmem⟩ := hfin v hv
  rw [hc, ← hpc] at habs
  exact habs hmem

theorem unchecked_double_mint_iff_misdeclared {srcOf decl : Value → Chain}
    {tree : Chain → Set Value} {v : Value} (hHI : HonestInsertion srcOf tree) :
    ((∃ c, FinalityUnchecked tree v c) ∧ ∃ c, RefundChecked decl tree v c)
      ↔ (v ∈ tree (srcOf v) ∧ decl v ≠ srcOf v) := by
  constructor
  · rintro ⟨⟨c, hmem⟩, ⟨c', hc', habs⟩⟩
    have hmem' : v ∈ tree c := hmem
    have hsrc : srcOf v = c := hHI c v hmem'
    have hlive : v ∈ tree (srcOf v) := by rw [hsrc]; exact hmem'
    refine ⟨hlive, fun heq => ?_⟩
    rw [hc', heq] at habs
    exact habs hlive
  · rintro ⟨hlive, hne⟩
    exact ⟨⟨srcOf v, hlive⟩, ⟨decl v, rfl, fun hmem => hne (hHI (decl v) v hmem).symm⟩⟩

theorem refund_blocked_iff_declared_is_source {srcOf decl : Value → Chain}
    {tree : Chain → Set Value} {v : Value} (hHI : HonestInsertion srcOf tree)
    (hlive : v ∈ tree (srcOf v)) :
    (¬ ∃ c, RefundChecked decl tree v c) ↔ decl v = srcOf v := by
  constructor
  · intro hno
    by_contra hne
    exact hno ⟨decl v, rfl, fun hmem => hne (hHI (decl v) v hmem).symm⟩
  · rintro heq ⟨c, hc, habs⟩
    rw [hc, heq] at habs
    exact habs hlive

theorem unchecked_exclusive_under_declared {decl : Value → Chain} {tree : Chain → Set Value}
    {legs : List Value} {pc : Value → Chain} (hDI : DeclaredInsertion decl tree)
    (hfin : FlowFinalizedUnchecked tree legs pc) :
    FlowFinalizedChecked decl tree legs pc ∧ ¬ FlowRefunded decl tree legs := by
  have hc : FlowFinalizedChecked decl tree legs pc :=
    fun v hv => ⟨(hDI (pc v) v (hfin v hv)).symm, hfin v hv⟩
  exact ⟨hc, checked_gates_exclusive hc⟩

theorem upgrade_checkA_redundant {srcOf decl : Value → Chain} {tree : Chain → Set Value}
    {legs : List Value} {pc : Value → Chain} (hR : UpgradeReach srcOf decl tree)
    (hfin : FlowFinalizedUnchecked tree legs pc) :
    FlowFinalizedChecked decl tree legs pc ∧ ¬ FlowRefunded decl tree legs :=
  unchecked_exclusive_under_declared (upgradeReach_declared hR).2 hfin

theorem upgrade_excludes_misdeclared {srcOf decl : Value → Chain} {tree : Chain → Set Value}
    {c : Chain} {v : Value} (hR : UpgradeReach srcOf decl tree) (hmem : v ∈ tree c) :
    decl v = srcOf v := by
  obtain ⟨hHI, hDI⟩ := upgradeReach_declared hR
  exact (hDI c v hmem).trans (hHI c v hmem).symm

/-! ## The countermodel -/

theorem cm_mem_true : () ∈ cmTree true := Or.inr ⟨rfl, rfl⟩

theorem cm_not_mem_false : () ∉ cmTree false := by
  intro h
  rcases h with h | ⟨h, _⟩
  · simp at h
  · simp at h

theorem cm_pinnedReach : PinnedReach cmSrc cmTree :=
  PinnedReach.append true () PinnedReach.genesis rfl

theorem pinned_misdeclared_double_mint : Properties.PinnedMisdeclaredDoubleMint := by
  refine ⟨cm_pinnedReach, pinnedReach_honest cm_pinnedReach, ?_, cm_mem_true, ?_, ?_, ?_, ?_⟩
  · intro hDI
    have h := hDI true () cm_mem_true
    simp [cmDecl] at h
  · simp [cmDecl, cmSrc]
  · intro v _
    cases v
    exact cm_mem_true
  · exact ⟨(), List.mem_singleton_self _, false, rfl, cm_not_mem_false⟩
  · intro pc h
    obtain ⟨hpc, hmem⟩ := h () (List.mem_singleton_self _)
    have hpc' : pc () = false := hpc
    rw [hpc'] at hmem
    exact cm_not_mem_false hmem

theorem refund_not_blocked_when_pinned_to_declared :
    Properties.RefundNotBlockedWhenPinnedToDeclared :=
  ⟨cm_pinnedReach, cm_mem_true, rfl, cm_not_mem_false⟩

theorem upgrade_finality_satisfiable : Properties.UpgradeFinalitySatisfiable := by
  refine ⟨UpgradeReach.append true () UpgradeReach.genesis rfl rfl, ?_, ?_⟩
  · intro v _
    cases v
    exact cm_mem_true
  · intro v _
    cases v
    exact ⟨rfl, cm_mem_true⟩

/-! ## Certificates -/

theorem PinnedReachHonest : Properties.PinnedReachHonest :=
  fun _ _ _ _ h => pinnedReach_honest h

theorem UpgradeReachDeclared : Properties.UpgradeReachDeclared :=
  fun _ _ _ _ _ h => upgradeReach_declared h

theorem CheckedGatesExclusive : Properties.CheckedGatesExclusive :=
  fun _ _ _ _ _ _ hfin => checked_gates_exclusive hfin

theorem UncheckedDoubleMintIffMisdeclared : Properties.UncheckedDoubleMintIffMisdeclared :=
  fun _ _ _ _ _ _ hHI => unchecked_double_mint_iff_misdeclared hHI

theorem PinnedMisdeclaredDoubleMint : Properties.PinnedMisdeclaredDoubleMint :=
  pinned_misdeclared_double_mint

theorem RefundNotBlockedWhenPinnedToDeclared : Properties.RefundNotBlockedWhenPinnedToDeclared :=
  refund_not_blocked_when_pinned_to_declared

theorem RefundBlockedIffDeclaredIsSource : Properties.RefundBlockedIffDeclaredIsSource :=
  fun _ _ _ _ _ _ hHI hlive => refund_blocked_iff_declared_is_source hHI hlive

theorem UncheckedExclusiveUnderDeclared : Properties.UncheckedExclusiveUnderDeclared :=
  fun _ _ _ _ _ _ hDI hfin => unchecked_exclusive_under_declared hDI hfin

theorem UpgradeCheckARedundant : Properties.UpgradeCheckARedundant :=
  fun _ _ _ _ _ _ _ hR hfin => upgrade_checkA_redundant hR hfin

theorem UpgradeExcludesMisdeclared : Properties.UpgradeExcludesMisdeclared :=
  fun _ _ _ _ _ _ _ hR hmem => upgrade_excludes_misdeclared hR hmem

theorem UpgradeFinalitySatisfiable : Properties.UpgradeFinalitySatisfiable :=
  upgrade_finality_satisfiable

end AttackVectors.ProofPolarityFaithful
