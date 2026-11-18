import EraSpec.Contracts.ValidatorTimelock.Properties.LibMap
import EraSpec.Contracts.ValidatorTimelock.Proofs.Model

/-!
# Proofs: the packed commit timestamps

Bit by bit (`Nat.eq_of_testBit_eq`): writing the 32-bit field at offset `o` reads back the new
value (`field_same`) and leaves every other 32-bit field of the slot alone (`field_other`);
other slots are untouched by `upd`. The loop is an induction on its iteration count.
-/

namespace Contracts.ValidatorTimelock

lemma and_seven (i : ℕ) : i &&& 7 = i % 8 := Nat.and_two_pow_sub_one_eq_mod i 3

lemma testBit_false_of_lt {x n i : ℕ} (hx : x < 2 ^ n) (hi : n ≤ i) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hi))

/-- Writing a 32-bit field at offset `o` and reading it back. -/
lemma field_same (w v o : ℕ) (ho : o + 32 ≤ 256) (hv : v < 2 ^ 32) :
    ((((((w >>> o) % 2 ^ 32) ^^^ v) <<< o) % 2 ^ 256 ^^^ w) >>> o) % 2 ^ 32 = v := by
  apply Nat.eq_of_testBit_eq
  intro b
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_xor,
    Nat.testBit_shiftLeft]
  by_cases hb : b < 32
  · have h1 : o + b < 256 := by omega
    have h2 : o + b ≥ o := by omega
    have h3 : o + b - o = b := by omega
    simp only [hb, h1, h2, h3, decide_true, Bool.true_and]
    cases w.testBit (o + b) <;> cases v.testBit b <;> rfl
  · simp only [hb, decide_false, Bool.false_and]
    exact (testBit_false_of_lt hv (by omega)).symm

/-- Writing a 32-bit field at offset `o` leaves the field at another offset `o'` alone. -/
lemma field_other (w x o o' : ℕ) (hx : x < 2 ^ 32) (ho : o % 32 = 0) (ho' : o' % 32 = 0)
    (hne : o ≠ o') :
    ((((x <<< o) % 2 ^ 256 ^^^ w) >>> o') % 2 ^ 32) = (w >>> o') % 2 ^ 32 := by
  apply Nat.eq_of_testBit_eq
  intro b
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_xor,
    Nat.testBit_shiftLeft]
  by_cases hb : b < 32
  · simp only [hb, decide_true, Bool.true_and]
    have hz : (decide (o' + b < 256) && (decide (o' + b ≥ o) && x.testBit (o' + b - o))) =
        false := by
      by_cases hlt : o' + b ≥ o
      · have : 32 ≤ o' + b - o := by omega
        rw [testBit_false_of_lt hx this]; simp
      · simp [hlt]
    rw [hz, Bool.false_xor]
  · simp [hb]

theorem LibMapGetFitsUint32 : Properties.LibMapGetFitsUint32 := by
  intro m i
  exact Nat.mod_lt _ (by norm_num)

theorem LibMapSetKeepsWords : Properties.LibMapSetKeepsWords := by
  intro m i v hm k
  simp only [libMapSet]
  by_cases hk : k = i / 8
  · subst hk
    rw [upd_same]
    exact Nat.xor_lt_two_pow (Nat.mod_lt _ (by norm_num)) (hm _)
  · rw [upd_other _ _ hk]; exact hm k

theorem LibMapGetSet : Properties.LibMapGetSet := by
  intro m i j v hm hv
  simp only [libMapGet, libMapSet, and_seven]
  by_cases hq : j / 8 = i / 8
  · rw [hq, upd_same]
    by_cases hji : j = i
    · subst hji
      rw [ite_eq_left rfl]
      exact field_same _ _ _ (by omega) hv
    · rw [ite_eq_right hji, ← hq]
      have hx : (m (j / 8) >>> (i % 8 * 32)) % 2 ^ 32 ^^^ v < 2 ^ 32 :=
        Nat.xor_lt_two_pow (Nat.mod_lt _ (by norm_num)) hv
      have hmod : i % 8 ≠ j % 8 := fun h => hji (by omega)
      exact field_other _ _ _ _ hx (by omega) (by omega) (by omega)
  · rw [upd_other _ _ hq]
    have hji : j ≠ i := fun h => hq (by rw [h])
    rw [ite_eq_right hji]

lemma recordLoop_spec (ts : ℕ) (hts : ts < 2 ^ 32) :
    ∀ (n i : ℕ) (m : Uint32Map), StorageWords m →
      StorageWords (recordLoop ts i n m) ∧
      ∀ j, libMapGet (recordLoop ts i n m) j = if i ≤ j ∧ j < i + n then ts else libMapGet m j
  | 0, i, m, hm => ⟨hm, fun j => by simp only [recordLoop]; rw [ite_eq_right (by omega)]⟩
  | n + 1, i, m, hm => by
      have hm' := LibMapSetKeepsWords m i ts hm
      obtain ⟨h1, h2⟩ := recordLoop_spec ts hts n (i + 1) (libMapSet m i ts) hm'
      refine ⟨h1, fun j => ?_⟩
      simp only [recordLoop]
      rw [h2 j, LibMapGetSet m i j ts hm hts]
      by_cases hj1 : i + 1 ≤ j ∧ j < i + 1 + n
      · rw [ite_eq_left hj1, ite_eq_left (by omega)]
      · rw [ite_eq_right hj1]
        by_cases hj2 : j = i
        · rw [ite_eq_left hj2, ite_eq_left (by omega)]
        · rw [ite_eq_right hj2, ite_eq_right (by omega)]

theorem RecordLoopWritesTheRange : Properties.RecordLoopWritesTheRange := by
  intro m lo hi now hm
  obtain ⟨h1, h2⟩ := recordLoop_spec (now % 2 ^ 32) (Nat.mod_lt _ (by norm_num)) (hi + 1 - lo)
    lo m hm
  refine ⟨h1, fun j => ?_⟩
  unfold recordBatchCommitment
  rw [h2 j]
  by_cases h : lo ≤ j ∧ j ≤ hi
  · rw [ite_eq_left (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right h]

lemma uint32_eq : UINT32 = 2 ^ 32 := by decide

lemma packedStep_of_not_commit {k : Call} (M : PackedTimestamps)
    (h : ∀ c lo hi, k.action ≠ .commitBatches c lo hi) : packedStep k M = M := by
  rcases k with ⟨e, x, a⟩
  cases a with
  | commitBatches c lo hi => exact absurd rfl (h c lo hi)
  | _ => rfl

lemma not_commits_of_not_commit {k : Call} (h : ∀ c lo hi, k.action ≠ .commitBatches c lo hi)
    (c : Address) (i : ℕ) : ¬ k.action.commits c i := by
  rcases k with ⟨e, x, a⟩
  cases a with
  | commitBatches c' lo hi => exact absurd rfl (h c' lo hi)
  | _ => exact fun h' => h'

theorem PackedTimestampsRefine : Properties.PackedTimestampsRefine := by
  refine ⟨fun c => ⟨fun _ => by norm_num, fun i => by simp [libMapGet, init]⟩, ?_⟩
  intro M k s s' hM h
  by_cases hk : ∃ c lo hi, k.action = .commitBatches c lo hi
  · obtain ⟨c, lo, hi, hka⟩ := hk
    have hs' : s' = recordCommit s c lo hi k.env.now := by
      rw [step_eq_of_action hka] at h
      exact (commitBatches_eq_some.mp h).2.2.2
    have hp : packedStep k M = upd M c (recordBatchCommitment (M c) lo hi k.env.now) := by
      rcases k with ⟨e, x, a⟩; simp only at hka; subst hka; rfl
    rw [hp, hs']
    intro c'
    by_cases hc : c' = c
    · subst hc
      rw [upd_same]
      obtain ⟨h1, h2⟩ := RecordLoopWritesTheRange (M c') lo hi k.env.now (hM c').1
      refine ⟨h1, fun i => ?_⟩
      rw [h2 i, (hM c').2 i]
      simp only [recordCommit, true_and, uint32_eq]
    · rw [upd_other _ _ hc]
      refine ⟨(hM c').1, fun i => ?_⟩
      rw [(hM c').2 i]
      simp [recordCommit, hc]
  · have hk' : ∀ c lo hi, k.action ≠ .commitBatches c lo hi := fun c lo hi h' =>
      hk ⟨c, lo, hi, h'⟩
    rw [packedStep_of_not_commit M hk']
    intro c
    refine ⟨(hM c).1, fun i => ?_⟩
    rw [(hM c).2 i, step_post h, post_committedAt_of_not_commits (not_commits_of_not_commit hk' c i)]

lemma packedRun_spec :
    ∀ {s s' : State} {ks : List Call}, Run s ks s' → ∀ {M : PackedTimestamps}, Represents M s →
      Represents (packedRun ks M) s'
  | _, _, _, .nil _, _, hM => hM
  | _, _, _, .cons (k := k) h1 h2, M, hM => by
      show Represents (packedRun _ (packedStep k M)) _
      exact packedRun_spec h2 (PackedTimestampsRefine.2 M k _ _ hM h1)

theorem PackedTimestampsRefineRuns : Properties.PackedTimestampsRefineRuns := by
  intro M s s' ks hM h
  exact packedRun_spec h hM

theorem PackedTimestampsWitness : Properties.PackedTimestampsWitness := by
  obtain ⟨s, h, e⟩ := exists_run_of_isSome (ks := vtSetupCalls ++ [vtDelayCommit]) (s := init)
    (by decide)
  exact ⟨s, h, packedRun_spec h PackedTimestampsRefine.1, by decide,
    map_of_exec e (fun s => s.committedAt vtChain 2) (by decide)⟩

theorem LibMapWitness : Properties.LibMapWitness := by
  refine ⟨fun k => ?_, by norm_num, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩
  unfold vtSlotMap
  split_ifs <;> norm_num

end Contracts.ValidatorTimelock
