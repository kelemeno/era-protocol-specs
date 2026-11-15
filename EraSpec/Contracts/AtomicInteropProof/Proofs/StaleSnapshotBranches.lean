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

theorem end_branch_gives_pin {H : BatchSnapshots} {D T v : UInt256} {B : ℕ}
    {W : AbsLeaf} (hlate : LaterBatchesLate B H.t T) (he : EndBranch H D T v B W) :
    W ∈ H.endS B ∧ D < H.t (B + 1) :=
  ⟨he.mem, lt_of_lt_of_le he.rootLate (hlate (B + 1) (Nat.lt_succ_self B))⟩

theorem laterBatchesLate_of_offset (H : AttackVectors.TimeoutSoundness.BatchHistory)
    (f p T : ℕ) :
    (∀ m, f + (p + 1) ≤ m → T ≤ H.time m) ↔
      LaterBatchesLate (AttackVectors.LastBatchInRootOffset.batchAt f p) H.time T := by
  unfold LaterBatchesLate AttackVectors.LastBatchInRootOffset.batchAt
  constructor
  · intro h m hm
    exact h m (by omega)
  · intro h m hm
    exact h m (by omega)

theorem outsideRootLate_gives_laterBatchesLate {inRoot : ℕ → Prop} {t : ℕ → UInt256}
    {T : UInt256} {B : ℕ} (hout : OutsideRootLate inRoot t T) (hlast : ∀ m, inRoot m → m ≤ B) :
    LaterBatchesLate B t T := by
  intro m hm
  exact hout m (fun hin => absurd (hlast m hin) (by omega))

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

theorem end_branch_not_redeemable {H : BatchSnapshots} {D T v : UInt256}
    {B : ℕ} {W : AbsLeaf} (hevo : Evolution H.endS) (h0 : SoundState (H.endS 0))
    (hlater : LaterBatchesLate B H.t T) (he : EndBranch H D T v B W) :
    ∀ i, H.t i ≤ D → v ∉ keys (H.endS i) := by
  intro i hti hmem
  have hiB : i ≤ B := by
    by_contra hgt
    have hlate : T ≤ H.t i := hlater i (by omega)
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

theorem end_branch_needs_laterBatchesLate : Properties.EndBranchNeedsLaterBatchesLate := by
  refine ⟨AttackVectors.Timestamps.attackHistory_evolution one_ne_zero_word,
    genesis_soundState, monotone_const, ?_, ?_,
    ⟨by decide, le_refl _, Finset.mem_singleton_self _, by decide, Or.inl rfl⟩,
    le_refl _, one_mem_insert_keys⟩
  · intro n
    cases n with
    | zero => rfl
    | succ m => simp [staleRootHistory]
  · intro hlate
    have h1 : (1 : UInt256) ≤ staleRootHistory.t 1 := hlate 1 (by norm_num)
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
    ⟨by decide, by decide, Finset.mem_singleton_self _, by decide, Or.inl rfl⟩, ?_⟩
  · intro m hm
    have hm1 : ¬ m ≤ 1 := by omega
    show (1 : UInt256) ≤ (if m ≤ 1 then (0 : UInt256) else 1)
    simp [hm1]
  · intro hout
    have h0 : (1 : UInt256) ≤ eraVMHonestHistory.t 0 := hout 0 (by norm_num)
    exact absurd h0 (by decide)

/-! ## Certificates -/

theorem BeginBranchGivesPin : Properties.BeginBranchGivesPin :=
  fun _ _ _ _ _ _ hbp hL hb => begin_branch_gives_pin hbp hL hb

theorem EndBranchGivesPin : Properties.EndBranchGivesPin :=
  fun _ _ _ _ _ _ hlate he => end_branch_gives_pin hlate he

theorem LaterBatchesLateOfOffset : Properties.LaterBatchesLateOfOffset :=
  laterBatchesLate_of_offset

theorem OutsideRootLateGivesLaterBatchesLate : Properties.OutsideRootLateGivesLaterBatchesLate :=
  fun _ _ _ _ hout hlast => outsideRootLate_gives_laterBatchesLate hout hlast

theorem BeginBranchNotRedeemable : Properties.BeginBranchNotRedeemable :=
  fun _ _ _ _ _ _ hevo h0 htmono hbp hb => begin_branch_not_redeemable hevo h0 htmono hbp hb

theorem EndBranchNotRedeemable : Properties.EndBranchNotRedeemable :=
  fun _ _ _ _ _ _ hevo h0 hlate he => end_branch_not_redeemable hevo h0 hlate he

theorem BeginBranchNeedsBeginIsPrevEnd : Properties.BeginBranchNeedsBeginIsPrevEnd :=
  begin_branch_needs_beginIsPrevEnd

theorem EndBranchNeedsLaterBatchesLate : Properties.EndBranchNeedsLaterBatchesLate :=
  end_branch_needs_laterBatchesLate

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
