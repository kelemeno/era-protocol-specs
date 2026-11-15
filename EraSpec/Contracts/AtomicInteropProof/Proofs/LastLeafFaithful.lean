import EraSpec.Contracts.AtomicInteropProof.Properties.LastLeafFaithful
import EraSpec.Contracts.AtomicInteropProof.Proofs.LastLeaf

/-! # Proofs: the last-leaf check with the path length and index the prover's
(see `../Specs/LastLeafFaithful.lean`) -/

namespace MerkleSpec.LastLeafFaithful

open MerkleSpec MerkleSpec.Verifier MerkleSpec.LastLeaf

/-! ## The headline -/

/-- The right-length case: the entry and the siblings are pinned, or the path collides. -/
theorem accepted_at_height (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256)
    (height j : ℕ) (x : UInt256) (hcap : L.length ≤ 2 ^ height)
    (hacc : LastBatchPathAccepted h z0 L height sibs height j x) :
    (j + 1 = L.length ∧ L.getD j z0 = x) ∨ (L.length ≤ j ∧ x = z0)
      ∨ PinnedBreak h z0 L j ∨ PathCollision h z0 L sibs 0 height j x := by
  have hroot : (levels h z0 L (0 + height)).getD (j / 2 ^ height) (zeros h z0 (0 + height))
      = rootOf h z0 L height := by
    rw [Nat.zero_add, Nat.div_eq_of_lt hacc.inBounds, rootOf_def, getD_zero_headD]
  rcases walk_pins_or_collision h z0 L sibs height 0 j x
      (by rw [hroot]; exact hacc.authenticated) with ⟨hentry, hpin⟩ | hc
  · have hentry' : L.getD j z0 = x := by simpa using hentry
    by_cases hj : j < L.length
    · have honest : ∀ l < height,
          sibs l = (levels h z0 L l).getD (sibIdx (j / 2 ^ l)) (zeros h z0 l) := by
        intro l hl
        have := hpin l (by omega) (by omega)
        rwa [Nat.sub_zero] at this
      rcases last_leaf_or_pinned_break h z0 L sibs height j hcap hj honest hacc.zeroCheck with
        hl | hp
      · exact Or.inl ⟨hl, hentry'⟩
      · exact Or.inr (Or.inr (Or.inl hp))
    · have hj' : L.length ≤ j := not_lt.mp hj
      refine Or.inr (Or.inl ⟨hj', ?_⟩)
      rw [← hentry', getD_default L j z0 hj']
  · exact Or.inr (Or.inr (Or.inr hc))

theorem accepted_last_leaf_any_length_or_break (h : Hash) (z0 : UInt256) (L : List UInt256)
    (sibs : ℕ → UInt256) (k height j : ℕ) (x : UInt256)
    (hcap : L.length ≤ 2 ^ height) (hacc : LastBatchPathAccepted h z0 L height sibs k j x) :
    (k = height ∧ j + 1 = L.length ∧ L.getD j z0 = x)
      ∨ LastLeafAnyLengthBreak h z0 L sibs k height j x := by
  rcases accept_forces_height_or_break h z0 L sibs k height j x hacc.inBounds
      hacc.authenticated with hk | hb
  · subst hk
    rcases accepted_at_height h z0 L sibs _ j x hcap hacc with ⟨hl, he⟩ | ⟨hle, hxz⟩ | hp | hc
    · exact Or.inl ⟨rfl, hl, he⟩
    · exact Or.inr (LastLeafAnyLengthBreak.paddedEntry rfl hle hxz)
    · exact Or.inr (LastLeafAnyLengthBreak.pinned rfl hp)
    · exact Or.inr (LastLeafAnyLengthBreak.pathCollision rfl hc)
  · exact Or.inr (LastLeafAnyLengthBreak.wrongLength hb)

/-! ## The two excluded cases are live -/

/-- No pinned break at leaf 0 of `[5, 7, 9]`: no level-`(l+1)` node starts at index 1,
and entry 1 is not the empty constant. -/
theorem demo_no_pinned_break_zero : ¬ PinnedBreak demoHash 0 [5, 7, 9] 0 := by
  rintro (⟨l, m, _, hm, _, _⟩ | ⟨_, he⟩)
  · have h2 : 2 ∣ m * 2 ^ (l + 1) :=
      Dvd.dvd.mul_left (dvd_pow_self 2 (Nat.succ_ne_zero l)) m
    rw [hm] at h2
    omega
  · exact absurd he (by decide)

theorem wrong_length_last_leaf_accepted : Properties.WrongLengthLastLeafAccepted := by
  refine ⟨demoHash, 0, [5, 7, 9], fun _ => 0, 0, 2, 0, rootOf demoHash 0 [5, 7, 9] 2,
    by decide,
    ⟨by norm_num, walkPure_zero _ _ _ _ _, fun l hl => absurd hl (Nat.not_lt_zero l)⟩,
    by decide, ?_, ?_⟩
  · rintro (hl | hp | ⟨i, hi, _⟩)
    · simp at hl
    · exact demo_no_pinned_break_zero hp
    · exact absurd hi (Nat.not_lt_zero i)
  · exact (zero_length_path_accepts_root demoHash 0 [5, 7, 9] (fun _ => 0) 2 (by norm_num)).2

theorem padded_index_last_leaf_accepted : Properties.PaddedIndexLastLeafAccepted := by
  refine ⟨demoHash, 0, [5], honestSibs demoHash 0 [5] 2, 2, 2, 2, 0, by decide,
    ⟨by norm_num, padded_slot_verifies demoHash 0 [5] 2 2 (by decide) (by norm_num), ?_⟩,
    ⟨0, by norm_num, by norm_num⟩, rfl, by decide, rfl, ?_,
    heightBreak_not_tautology.1 _ _ _ _ _ _ _⟩
  · intro l hl hev
    interval_cases l
    · decide
    · norm_num at hev
  · rintro (hl | hp | hc)
    · simp at hl
    · exact no_pinned_break_at_end demoHash 0 [5] 2 (by decide) hp
    · exact honest_walk_no_collision demoHash 0 [5] 2 2 hc

theorem any_length_conclusion_not_always : Properties.AnyLengthConclusionNotAlways := by
  refine ⟨demoHash, 0, [5, 7, 9], honestSibs demoHash 0 [5, 7, 9] 1, 2, 2, 1,
    ([5, 7, 9] : List UInt256).getD 1 0, by decide, by norm_num,
    honest_walk_root demoHash 0 [5, 7, 9] 2 1 (by norm_num), ?_⟩
  rintro (⟨_, hl, _⟩ | hb)
  · simp at hl
  · cases hb with
    | wrongLength hh => exact heightBreak_not_tautology.1 _ _ _ _ _ _ _ hh
    | paddedEntry _ hle _ => simp at hle
    | pinned _ hp => exact demo_no_pinned_break hp
    | pathCollision _ hc => exact honest_walk_no_collision demoHash 0 [5, 7, 9] 2 1 hc

/-! ## The recovered forms -/

theorem accepted_last_leaf_pinned_length_or_break (h : Hash) (z0 : UInt256) (L : List UInt256)
    (sibs : ℕ → UInt256) (k height j : ℕ) (x : UInt256)
    (hcap : L.length ≤ 2 ^ height) (hacc : LastBatchPathAccepted h z0 L height sibs k j x)
    (hk : k = height) (hx : x ≠ z0) :
    j + 1 = L.length ∨ PinnedBreak h z0 L j ∨ PathCollision h z0 L sibs 0 k j x := by
  rcases accepted_last_leaf_any_length_or_break h z0 L sibs k height j x hcap hacc with
    ⟨_, hl, _⟩ | hb
  · exact Or.inl hl
  · cases hb with
    | wrongLength hh =>
      subst hk
      exact absurd hh (heightBreak_not_tautology.1 _ _ _ _ _ _ _)
    | paddedEntry _ _ hxz => exact absurd hxz hx
    | pinned _ hp => exact Or.inr (Or.inl hp)
    | pathCollision _ hc => exact Or.inr (Or.inr hc)

theorem accepted_last_leaf_any_length_on (h : Hash) (z0 : UInt256) (L : List UInt256)
    (sibs : ℕ → UInt256) (k height j : ℕ) (x : UInt256)
    (hcap : L.length ≤ 2 ^ height) (hacc : LastBatchPathAccepted h z0 L height sibs k j x)
    (hk : k = height) (hx : x ≠ z0) (hsep : EntriesNotEmpty z0 L)
    (hinj : PairInjOn h (fun p => TreePair h z0 L height p ∨ PathTreePair h z0 L height j p
      ∨ VerifiedPair h sibs height j x p)) :
    j + 1 = L.length := by
  rcases accepted_last_leaf_pinned_length_or_break h z0 L sibs k height j x hcap hacc hk hx with
    hl | hp | ⟨i, hi, hne, heq⟩
  · exact hl
  · exact absurd hp (no_pinned_break_on h z0 L height j hcap hsep
      (pairInjOn_mono hinj (fun p hp => Or.inl hp)))
  · subst hk
    exact absurd (hinj _ _ (Or.inr (Or.inr ⟨i, hi, rfl⟩))
      (Or.inr (Or.inl ⟨i, hi, by rw [Nat.zero_add]⟩)) heq) hne

/-- Every pair in the extended bounded set of the demo instance is one of four explicit
pairs (the tree's pairs along index 1's path are already among them). -/
lemma demo_pairs_mem' (p : UInt256 × UInt256)
    (hp : TreePair demoHash 0 [5, 7] 2 p ∨ PathTreePair demoHash 0 [5, 7] 2 1 p
      ∨ VerifiedPair demoHash (honestSibs demoHash 0 [5, 7] 1) 2 1 7 p) :
    p ∈ ([(5, 7), (20, 1), (0, 0), (1, 1)] : List (UInt256 × UInt256)) := by
  rcases hp with hp | ⟨i, hi, rfl⟩ | hp
  · exact demo_pairs_mem p (Or.inl hp)
  · interval_cases i <;> decide
  · exact demo_pairs_mem p (Or.inr hp)

theorem demo_pairInjOn' : PairInjOn demoHash (fun p => TreePair demoHash 0 [5, 7] 2 p
    ∨ PathTreePair demoHash 0 [5, 7] 2 1 p
    ∨ VerifiedPair demoHash (honestSibs demoHash 0 [5, 7] 1) 2 1 7 p) := by
  have hW : ∀ p ∈ ([(5, 7), (20, 1), (0, 0), (1, 1)] : List (UInt256 × UInt256)),
      ∀ q ∈ ([(5, 7), (20, 1), (0, 0), (1, 1)] : List (UInt256 × UInt256)),
        demoHash p.1 p.2 = demoHash q.1 q.2 → p = q := by
    intro p hp q hq he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp hq
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
      first | rfl | exact absurd he (by decide)
  exact fun p q hp hq he => hW p (demo_pairs_mem' p hp) q (demo_pairs_mem' q hq) he

theorem accepted_last_leaf_any_length_on_satisfiable :
    Properties.AcceptedLastLeafAnyLengthOnSatisfiable := by
  refine ⟨demoHash, 0, [5, 7], honestSibs demoHash 0 [5, 7] 1, 2, 2, 1, 7, by decide,
    ⟨by norm_num, by decide, ?_⟩, rfl, by decide, demo_entriesNotEmpty, demo_pairInjOn',
    ⟨1, by norm_num, by decide⟩, demo_collides⟩
  intro l hl hev
  interval_cases l
  · norm_num at hev
  · decide

/-! ## Certificates -/

theorem AcceptedLastLeafAnyLengthOrBreak : Properties.AcceptedLastLeafAnyLengthOrBreak :=
  accepted_last_leaf_any_length_or_break

theorem WrongLengthLastLeafAccepted : Properties.WrongLengthLastLeafAccepted :=
  wrong_length_last_leaf_accepted

theorem PaddedIndexLastLeafAccepted : Properties.PaddedIndexLastLeafAccepted :=
  padded_index_last_leaf_accepted

theorem AnyLengthConclusionNotAlways : Properties.AnyLengthConclusionNotAlways :=
  any_length_conclusion_not_always

theorem AcceptedLastLeafPinnedLengthOrBreak : Properties.AcceptedLastLeafPinnedLengthOrBreak :=
  accepted_last_leaf_pinned_length_or_break

theorem AcceptedLastLeafAnyLengthOn : Properties.AcceptedLastLeafAnyLengthOn :=
  accepted_last_leaf_any_length_on

theorem AcceptedLastLeafAnyLengthOnSatisfiable :
    Properties.AcceptedLastLeafAnyLengthOnSatisfiable :=
  accepted_last_leaf_any_length_on_satisfiable

end MerkleSpec.LastLeafFaithful
