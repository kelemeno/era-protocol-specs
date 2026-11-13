import EraSpec.Contracts.AtomicInteropProof.Properties.StaleSnapshotBranches
import EraSpec.Contracts.AtomicInteropProof.Proofs.StaleSnapshot
import EraSpec.Contracts.AtomicInteropProof.Proofs.Timestamps
import EraSpec.Contracts.IndexedMerkleTree.Proofs.Model

/-! # Proofs: the stale-snapshot pin on the two deployed branches
(see `../Specs/StaleSnapshotBranches.lean`) -/

namespace AttackVectors.StaleSnapshotBranches

open IMTAbstract

/-! ## From each branch to the pin -/

theorem begin_branch_gives_pin {H : BatchSnapshots} {D T v : UInt256} {L : ℕ} {W : AbsLeaf}
    (hbp : BeginIsPrevEnd H) (hL : 0 < L) (hb : BeginBranch H D T v L W) :
    W ∈ H.endS (L - 1) ∧ D < H.t (L - 1 + 1) := by
  cases L with
  | zero => exact absurd hL (lt_irrefl 0)
  | succ n =>
    refine ⟨?_, ?_⟩
    · rw [Nat.add_sub_cancel, ← hbp n]
      exact hb.mem
    · rw [Nat.add_sub_cancel]
      exact hb.late

theorem end_branch_gives_pin {H : BatchSnapshots} {inRoot : ℕ → Prop} {D T v : UInt256} {B : ℕ}
    {W : AbsLeaf} (hout : OutsideRootLate inRoot H.t T) (he : EndBranch H inRoot D T v B W) :
    W ∈ H.endS B ∧ D < H.t (B + 1) := by
  refine ⟨he.mem, lt_of_lt_of_le he.rootLate (hout (B + 1) (fun hin => ?_))⟩
  have := he.lastInRoot (B + 1) hin
  omega

/-! ## The headline on each branch -/

theorem begin_branch_not_redeemable {H : BatchSnapshots} {D T v : UInt256} {L : ℕ} {W : AbsLeaf}
    (hevo : Evolution H.endS) (h0 : SoundState (H.endS 0)) (htmono : Monotone H.t)
    (hbp : BeginIsPrevEnd H) (hb : BeginBranch H D T v L W) :
    ∀ i, H.t i ≤ D → v ∉ keys (H.endS i) := by
  cases L with
  | zero =>
    intro i hti _
    exact absurd (lt_of_lt_of_le hb.late (htmono (Nat.zero_le i))) (not_lt.mpr hti)
  | succ n =>
    obtain ⟨hW, hpin⟩ := begin_branch_gives_pin hbp (by omega : 0 < n + 1) hb
    rw [Nat.add_sub_cancel] at hW hpin
    exact AttackVectors.StaleSnapshot.stale_witness_not_redeemable hevo h0 htmono hpin hW
      hb.window.1 hb.window.2

theorem end_branch_not_redeemable {H : BatchSnapshots} {inRoot : ℕ → Prop} {D T v : UInt256}
    {B : ℕ} {W : AbsLeaf} (hevo : Evolution H.endS) (h0 : SoundState (H.endS 0))
    (hout : OutsideRootLate inRoot H.t T) (he : EndBranch H inRoot D T v B W) :
    ∀ i, H.t i ≤ D → v ∉ keys (H.endS i) := by
  intro i hti hmem
  have hiB : i ≤ B := by
    by_contra hgt
    have hlate : T ≤ H.t i := hout i (fun hin => hgt (he.lastInRoot i hin))
    exact absurd (lt_of_lt_of_le he.rootLate hlate) (not_lt.mpr hti)
  have hkeys : v ∈ keys (H.endS B) := evolution_keys_mono hevo hiB hmem
  exact present_not_reclaimable (evolution_sound hevo h0 B).1 hkeys
    ⟨W, he.mem, he.window.1, he.window.2⟩

/-! ## The countermodels -/

theorem one_ne_zero_word : (1 : UInt256) ≠ 0 := by decide

theorem one_mem_insert_keys :
    (1 : UInt256) ∈ keys (imtInsert ({⟨0, 0⟩} : Finset AbsLeaf) ⟨0, 0⟩ 1) :=
  imtInsert_key_mem (Finset.mem_singleton_self _)

theorem one_not_mem_genesis_keys : (1 : UInt256) ∉ keys ({⟨0, 0⟩} : Finset AbsLeaf) := by
  intro hmem
  obtain ⟨X, hX, hk⟩ := Finset.mem_image.mp hmem
  rw [Finset.mem_singleton] at hX
  subst hX
  exact absurd hk (by decide)

theorem begin_branch_needs_beginIsPrevEnd : Properties.BeginBranchNeedsBeginIsPrevEnd := by
  refine ⟨AttackVectors.Timestamps.attackHistory_evolution one_ne_zero_word,
    genesis_soundState, ?_, ?_, ⟨by decide, by decide, Finset.mem_singleton_self _, by decide,
    Or.inl rfl⟩, by decide, one_mem_insert_keys⟩
  · intro m n hmn
    show (if m ≤ 1 then (0 : UInt256) else 1) ≤ (if n ≤ 1 then (0 : UInt256) else 1)
    split_ifs with h1 h2 h2
    · exact le_refl _
    · decide
    · exact absurd (le_trans hmn h2) h1
    · exact le_refl _
  · intro hbp
    have h1 : unlinkedHistory.beginS 2 = unlinkedHistory.endS 1 := hbp 1
    have hmem : (1 : UInt256) ∈ keys (unlinkedHistory.endS 1) := one_mem_insert_keys
    rw [← h1] at hmem
    exact one_not_mem_genesis_keys hmem

theorem end_branch_needs_outsideRootLate : Properties.EndBranchNeedsOutsideRootLate := by
  refine ⟨AttackVectors.Timestamps.attackHistory_evolution one_ne_zero_word,
    genesis_soundState, monotone_const, ?_, ?_,
    ⟨by decide, le_refl _, fun _ hm => hm, Finset.mem_singleton_self _, by decide, Or.inl rfl⟩,
    le_refl _, one_mem_insert_keys⟩
  · intro n
    cases n with
    | zero => rfl
    | succ m => simp [staleRootHistory]
  · intro hout
    have h1 : (1 : UInt256) ≤ staleRootHistory.t 1 := hout 1 (by norm_num)
    exact absurd h1 (by decide)

/-! ## What the pin means -/

theorem pin_bounds_on_time {t : ℕ → UInt256} {D : UInt256} {j : ℕ} (htmono : Monotone t)
    (hpin : D < t (j + 1)) : ∀ i, t i ≤ D → i ≤ j := by
  intro i hti
  by_contra hgt
  have : t (j + 1) ≤ t i := htmono (by omega)
  exact absurd (lt_of_lt_of_le hpin this) (not_lt.mpr hti)

theorem pin_does_not_make_snapshot_on_time : Properties.PinDoesNotMakeSnapshotOnTime :=
  ⟨fun _ => 1, 0, 0, monotone_const, by decide, by decide⟩

theorem begin_branch_pin_may_be_late : Properties.BeginBranchPinMayBeLate :=
  ⟨⟨fun _ => {⟨0, 0⟩}, fun _ => {⟨0, 0⟩}, fun _ => 1⟩, 0, 1, 1, 1, ⟨0, 0⟩, fun _ => rfl,
    ⟨by decide, by decide, Finset.mem_singleton_self _, by decide, Or.inl rfl⟩,
    by decide, by decide⟩

/-! ## Satisfiability of the headline premises -/

theorem honestHistory_monotone : Monotone honestHistory.t := by
  intro m n hmn
  show (if m = 0 then (0 : UInt256) else 1) ≤ (if n = 0 then (0 : UInt256) else 1)
  split_ifs with h1 h2 h2
  · exact le_refl _
  · decide
  · exact absurd (by omega : m = 0) h1
  · exact le_refl _

theorem begin_branch_not_redeemable_satisfiable :
    Properties.BeginBranchNotRedeemableSatisfiable :=
  ⟨fun _ => Or.inl rfl, genesis_soundState, honestHistory_monotone, fun _ => rfl,
    ⟨by decide, by decide, Finset.mem_singleton_self _, by decide, Or.inl rfl⟩, by decide⟩

theorem end_branch_not_redeemable_satisfiable :
    Properties.EndBranchNotRedeemableSatisfiable := by
  refine ⟨fun _ => Or.inl rfl, genesis_soundState, ?_,
    ⟨by decide, by decide, fun _ hm => hm, Finset.mem_singleton_self _, by decide, Or.inl rfl⟩⟩
  intro n hn
  have hn0 : n ≠ 0 := by omega
  show (1 : UInt256) ≤ (if n = 0 then (0 : UInt256) else 1)
  simp [hn0]

/-! ## Certificates -/

theorem BeginBranchGivesPin : Properties.BeginBranchGivesPin :=
  fun _ _ _ _ _ _ hbp hL hb => begin_branch_gives_pin hbp hL hb

theorem EndBranchGivesPin : Properties.EndBranchGivesPin :=
  fun _ _ _ _ _ _ _ hout he => end_branch_gives_pin hout he

theorem BeginBranchNotRedeemable : Properties.BeginBranchNotRedeemable :=
  fun _ _ _ _ _ _ hevo h0 htmono hbp hb => begin_branch_not_redeemable hevo h0 htmono hbp hb

theorem EndBranchNotRedeemable : Properties.EndBranchNotRedeemable :=
  fun _ _ _ _ _ _ _ hevo h0 hout he => end_branch_not_redeemable hevo h0 hout he

theorem BeginBranchNeedsBeginIsPrevEnd : Properties.BeginBranchNeedsBeginIsPrevEnd :=
  begin_branch_needs_beginIsPrevEnd

theorem EndBranchNeedsOutsideRootLate : Properties.EndBranchNeedsOutsideRootLate :=
  end_branch_needs_outsideRootLate

theorem PinBoundsOnTime : Properties.PinBoundsOnTime :=
  fun _ _ _ htmono hpin => pin_bounds_on_time htmono hpin

theorem PinDoesNotMakeSnapshotOnTime : Properties.PinDoesNotMakeSnapshotOnTime :=
  pin_does_not_make_snapshot_on_time

theorem BeginBranchPinMayBeLate : Properties.BeginBranchPinMayBeLate :=
  begin_branch_pin_may_be_late

theorem BeginBranchNotRedeemableSatisfiable : Properties.BeginBranchNotRedeemableSatisfiable :=
  begin_branch_not_redeemable_satisfiable

theorem EndBranchNotRedeemableSatisfiable : Properties.EndBranchNotRedeemableSatisfiable :=
  end_branch_not_redeemable_satisfiable

end AttackVectors.StaleSnapshotBranches
