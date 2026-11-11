import EraSpec.Contracts.AtomicInteropProof.Properties.LastLeaf
import EraSpec.Contracts.Merkle.Proofs.Verifier
import EraSpec.Contracts.Merkle.Proofs.PathCollision

/-! # Proofs: the last-leaf check (see `../Specs/LastLeaf.lean`) -/

namespace MerkleSpec.LastLeaf

open Clear MerkleSpec MerkleSpec.Verifier


/-- Assuming both idealizations, a break is impossible. -/
theorem not_hashBreak {h : Hash} {z0 : UInt256} {L : List UInt256}
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (hsep : EntriesNotEmpty z0 L) : ¬ HashBreak h z0 L := by
  intro hb
  cases hb with
  | nodeCollision a b c d hne heq =>
    rcases hne with hac | hbd
    · exact hac (hinj a b c d heq).1
    · exact hbd (hinj a b c d heq).2
  | entryIsEmpty m hm heq => exact hsep m hm heq

/-! ## A zero node over an occupied subtree -/

/-- **A ZERO NODE CANNOT SIT OVER AN OCCUPIED LEAF.**  If the level-`l` node at `m`
reads as `zeros l` while the first leaf under it is occupied, peel the zero cascade:
either some node's children are not both zeros — a collision — or an occupied entry
is the empty constant.

No injectivity assumed. -/
theorem zero_subtree_or_break (h : Hash) (z0 : UInt256) (L : List UInt256) :
    ∀ (l m : ℕ), m * 2 ^ l < L.length →
      (levels h z0 L l).getD m (zeros h z0 l) = zeros h z0 l → HashBreak h z0 L := by
  intro l
  induction l with
  | zero =>
    intro m hm heq
    refine HashBreak.entryIsEmpty m (by simpa using hm) ?_
    simpa using heq
  | succ l ih =>
    intro m hm heq
    rw [levels_succ_getD, zeros_succ] at heq
    by_cases hA : (levels h z0 L l).getD (2 * m) (zeros h z0 l) = zeros h z0 l
    · by_cases hB : (levels h z0 L l).getD (2 * m + 1) (zeros h z0 l) = zeros h z0 l
      · refine ih (2 * m) ?_ hA
        have : 2 * m * 2 ^ l = m * 2 ^ (l + 1) := by rw [pow_succ]; ring
        rw [this]
        exact hm
      · exact HashBreak.nodeCollision _ _ _ _ (Or.inr hB) heq
    · exact HashBreak.nodeCollision _ _ _ _ (Or.inl hA) heq

/-! ## Where the path first goes left -/

private lemma div_pow_succ (N l : ℕ) : N / 2 ^ (l + 1) = N / 2 / 2 ^ l := by
  rw [Nat.div_div_eq_div_mul, mul_comm, ← pow_succ]

/-- **THE FIRST LEFT TURN SITS EXACTLY ABOVE `j + 1`.**  Below it every step went
right, so `j`'s low bits are all ones and the right sibling's subtree begins at
`j + 1`. -/
theorem exists_left_level : ∀ (height N : ℕ), N + 1 < 2 ^ height →
    ∃ l < height, N / 2 ^ l % 2 = 0 ∧ (N / 2 ^ l + 1) * 2 ^ l = N + 1 := by
  intro height
  induction height with
  | zero =>
    intro N hN
    rw [pow_zero] at hN
    omega
  | succ height ih =>
    intro N hN
    by_cases hpar : N % 2 = 0
    · exact ⟨0, by omega, by simpa using hpar, by simp⟩
    · have hN2 : N / 2 + 1 < 2 ^ height := by
        rw [pow_succ] at hN
        omega
      obtain ⟨l, hl, hev, heq⟩ := ih (N / 2) hN2
      refine ⟨l + 1, by omega, ?_, ?_⟩
      · rw [div_pow_succ]
        exact hev
      · rw [div_pow_succ, pow_succ, ← mul_assoc, heq]
        omega

/-! ## The theorem -/

/-- **THE CHECK IDENTIFIES THE LAST LEAF, OR BREAKS THE HASH.**  Stated over the
tree's own siblings, with no injectivity: if every left-child sibling on `j`'s path
is the empty-subtree hash, then `j` is the last occupied leaf — or a break is
exhibited. -/
theorem last_leaf_or_break (h : Hash) (z0 : UInt256) (L : List UInt256)
    (sibs : ℕ → UInt256) (height j : ℕ)
    (hcap : L.length ≤ 2 ^ height) (hj : j < L.length)
    (honest : ∀ l < height, sibs l = (levels h z0 L l).getD (sibIdx (j / 2 ^ l)) (zeros h z0 l))
    (hzero : ∀ l < height, (j / 2 ^ l) % 2 = 0 → sibs l = zeros h z0 l) :
    j + 1 = L.length ∨ HashBreak h z0 L := by
  by_cases hlast : j + 1 = L.length
  · exact Or.inl hlast
  · refine Or.inr ?_
    have hnext : j + 1 < L.length := by omega
    obtain ⟨l, hl, hev, heq⟩ := exists_left_level height j (lt_of_lt_of_le hnext hcap)
    have hsib : (levels h z0 L l).getD (j / 2 ^ l + 1) (zeros h z0 l) = zeros h z0 l := by
      have h1 := honest l hl
      rw [hzero l hl hev, show sibIdx (j / 2 ^ l) = j / 2 ^ l + 1 from by simp [sibIdx, hev]] at h1
      exact h1.symm
    exact zero_subtree_or_break h z0 L l (j / 2 ^ l + 1) (by rw [heq]; exact hnext) hsib

/-- **AND THE SAME FOR AN AUTHENTICATED PATH.**  When the path recomputes the tree's
own root, its siblings *are* the tree's (`MerkleSpec.Verifier.walk_pins`), so the
check's conclusion holds for the proof as submitted. -/
theorem accepted_last_leaf_or_break (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L : List UInt256) (sibs : ℕ → UInt256) (height j : ℕ) (x : UInt256)
    (hcap : L.length ≤ 2 ^ height) (hj : j < L.length)
    (haccept : walkPure h sibs 0 height j x = rootOf h z0 L height)
    (hzero : ∀ l < height, (j / 2 ^ l) % 2 = 0 → sibs l = zeros h z0 l) :
    j + 1 = L.length ∨ HashBreak h z0 L := by
  refine last_leaf_or_break h z0 L sibs height j hcap hj ?_ hzero
  have hjcap : j < 2 ^ height := lt_of_lt_of_le hj hcap
  have hroot : (levels h z0 L (0 + height)).getD (j / 2 ^ height) (zeros h z0 (0 + height))
      = rootOf h z0 L height := by
    rw [Nat.zero_add, Nat.div_eq_of_lt hjcap, rootOf_def, getD_zero_headD]
  have hpin := (walk_pins h z0 hinj L sibs height 0 j x (by rw [hroot]; exact haccept)).2
  intro l hl
  have := hpin l (by omega) (by omega)
  rwa [Nat.sub_zero] at this

/-! ## Certificates -/

theorem NotHashBreak : Properties.NotHashBreak := @not_hashBreak
theorem LastLeafOrBreak : Properties.LastLeafOrBreak := last_leaf_or_break
theorem AcceptedLastLeafOrBreak : Properties.AcceptedLastLeafOrBreak := accepted_last_leaf_or_break


theorem HashBreakAlways : Properties.HashBreakAlways := by
  intro h z0 L
  obtain ⟨a, b, c, d, hne, he⟩ := MerkleSpec.Verifier.exists_pair_collision h
  refine .nodeCollision a b c d ?_ he
  by_contra hcd
  push_neg at hcd
  exact hne (by rw [hcd.1, hcd.2])

/-! ## Pinned forms -/

/-- **`zero_subtree_or_break`, PINNED.**  The node at level `l`, index `m`, whose
subtree starts at the occupied leaf `j + 1`, reads as `zeros l`.  Peeling the zero
cascade down the LEFT edge of that subtree visits only nodes whose subtree starts at
`j + 1`, so the break it finds is a `PinnedBreak` at `j`. -/
theorem zero_subtree_or_pinned_break (h : Hash) (z0 : UInt256) (L : List UInt256) (j : ℕ)
    (hnext : j + 1 < L.length) :
    ∀ (l m : ℕ), m * 2 ^ l = j + 1 →
      (levels h z0 L l).getD m (zeros h z0 l) = zeros h z0 l → PinnedBreak h z0 L j := by
  intro l
  induction l with
  | zero =>
    intro m hm heq
    rw [pow_zero, Nat.mul_one] at hm
    subst hm
    exact PinnedBreak.entryIsEmpty hnext (by simpa using heq)
  | succ l ih =>
    intro m hm heq
    rw [levels_succ_getD, zeros_succ] at heq
    by_cases hc : childPair h z0 L l m = zeroPair h z0 l
    · have hA : (levels h z0 L l).getD (2 * m) (zeros h z0 l) = zeros h z0 l :=
        congrArg Prod.fst hc
      refine ih (2 * m) ?_ hA
      rw [← hm, pow_succ]
      ring
    · exact PinnedBreak.nodeCollision l m hnext hm hc heq

/-- **THE CHECK IDENTIFIES THE LAST LEAF, OR A PINNED BREAK.** -/
theorem last_leaf_or_pinned_break (h : Hash) (z0 : UInt256) (L : List UInt256)
    (sibs : ℕ → UInt256) (height j : ℕ)
    (hcap : L.length ≤ 2 ^ height) (hj : j < L.length)
    (honest : ∀ l < height, sibs l = (levels h z0 L l).getD (sibIdx (j / 2 ^ l)) (zeros h z0 l))
    (hzero : ∀ l < height, (j / 2 ^ l) % 2 = 0 → sibs l = zeros h z0 l) :
    j + 1 = L.length ∨ PinnedBreak h z0 L j := by
  by_cases hlast : j + 1 = L.length
  · exact Or.inl hlast
  · refine Or.inr ?_
    have hnext : j + 1 < L.length := by omega
    obtain ⟨l, hl, hev, heq⟩ := exists_left_level height j (lt_of_lt_of_le hnext hcap)
    have hsib : (levels h z0 L l).getD (j / 2 ^ l + 1) (zeros h z0 l) = zeros h z0 l := by
      have h1 := honest l hl
      rw [hzero l hl hev, show sibIdx (j / 2 ^ l) = j / 2 ^ l + 1 from by simp [sibIdx, hev]] at h1
      exact h1.symm
    exact zero_subtree_or_pinned_break h z0 L j hnext l (j / 2 ^ l + 1) heq hsib

theorem no_pinned_break_at_end (h : Hash) (z0 : UInt256) (L : List UInt256) (j : ℕ)
    (hend : L.length ≤ j + 1) : ¬ PinnedBreak h z0 L j := by
  rintro (⟨_, _, hnext, _, _, _⟩ | ⟨hnext, _⟩) <;> omega

/-- The concrete non-last instance: leaves `[5, 7, 9]`, leaf `1`, `demoHash`. -/
theorem demo_no_pinned_break : ¬ PinnedBreak demoHash 0 [5, 7, 9] 1 := by
  rintro (⟨l, m, _, hm, _, heq⟩ | ⟨_, he⟩)
  · rcases l with _ | l
    · have hm1 : m = 1 := by simp at hm; omega
      subst hm1
      exact absurd heq (by decide)
    · exfalso
      have h4 : 4 ≤ 2 ^ (l + 1 + 1) :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (l + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rcases m with _ | m
      · simp at hm
      · nlinarith
  · exact absurd he (by decide)

theorem pinned_break_not_always : Properties.PinnedBreakNotAlways :=
  ⟨demoHash, 0, [5, 7, 9], 1, ⟨2, 0, 0, 1, by decide, by decide⟩, by decide,
    demo_no_pinned_break⟩

/-- **AN ACCEPTED SUBMITTED PATH: LAST LEAF, A PINNED BREAK, OR A PATH COLLISION.** -/
theorem accepted_last_leaf_or_pinned_break (h : Hash) (z0 : UInt256)
    (L : List UInt256) (sibs : ℕ → UInt256) (height j : ℕ) (x : UInt256)
    (hcap : L.length ≤ 2 ^ height) (hj : j < L.length)
    (haccept : walkPure h sibs 0 height j x = rootOf h z0 L height)
    (hzero : ∀ l < height, (j / 2 ^ l) % 2 = 0 → sibs l = zeros h z0 l) :
    j + 1 = L.length ∨ PinnedBreak h z0 L j ∨ PathCollision h z0 L sibs 0 height j x := by
  have hjcap : j < 2 ^ height := lt_of_lt_of_le hj hcap
  have hroot : (levels h z0 L (0 + height)).getD (j / 2 ^ height) (zeros h z0 (0 + height))
      = rootOf h z0 L height := by
    rw [Nat.zero_add, Nat.div_eq_of_lt hjcap, rootOf_def, getD_zero_headD]
  rcases walk_pins_or_collision h z0 L sibs height 0 j x (by rw [hroot]; exact haccept) with
    ⟨_, hpin⟩ | hc
  · have honest : ∀ l < height,
        sibs l = (levels h z0 L l).getD (sibIdx (j / 2 ^ l)) (zeros h z0 l) := by
      intro l hl
      have := hpin l (by omega) (by omega)
      rwa [Nat.sub_zero] at this
    rcases last_leaf_or_pinned_break h z0 L sibs height j hcap hj honest hzero with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr hc)

theorem accepted_last_leaf_or_pinned_break_satisfiable :
    Properties.AcceptedLastLeafOrPinnedBreakSatisfiable :=
  ⟨demoHash, 0, [5, 7], honestSibs demoHash 0 [5, 7] 1, 2, 1, 7,
    by decide, by decide, by decide, by decide, ⟨1, by decide, by decide⟩⟩

theorem accepted_pinned_conclusion_not_always : Properties.AcceptedPinnedConclusionNotAlways := by
  refine ⟨demoHash, 0, [5, 7, 9], honestSibs demoHash 0 [5, 7, 9] 1, 2, 1,
    ([5, 7, 9] : List UInt256).getD 1 0, by decide, by decide,
    honest_walk_root demoHash 0 [5, 7, 9] 2 1 (by norm_num), ?_⟩
  rintro (hl | hb | hc)
  · simp at hl
  · exact demo_no_pinned_break hb
  · exact honest_walk_no_collision demoHash 0 [5, 7, 9] 2 1 hc

theorem pairInjOn_mono {h : Hash} {P Q : UInt256 × UInt256 → Prop} (hP : PairInjOn h P)
    (hQP : ∀ p, Q p → P p) : PairInjOn h Q :=
  fun p q hp hq he => hP p q (hQP p hp) (hQP q hq) he

/-- **NO PINNED BREAK UNDER A BOUNDED NO-COLLISION PREMISE.** -/
theorem no_pinned_break_on (h : Hash) (z0 : UInt256) (L : List UInt256) (height j : ℕ)
    (hcap : L.length ≤ 2 ^ height) (hsep : EntriesNotEmpty z0 L)
    (hinj : PairInjOn h (TreePair h z0 L height)) : ¬ PinnedBreak h z0 L j := by
  rintro (⟨l, m, hnext, hm, hne, heq⟩ | ⟨hnext, he⟩)
  · apply hne
    have hm1 : 1 ≤ m := by
      rcases m with _ | m
      · simp at hm
      · omega
    have hlt : 2 ^ (l + 1) < 2 ^ height := by
      have : 2 ^ (l + 1) ≤ m * 2 ^ (l + 1) := by nlinarith
      omega
    have hl : l < height := by
      by_contra hcon
      have : 2 ^ height ≤ 2 ^ (l + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact hinj _ _ (Or.inl ⟨l, hl, m, by omega, rfl⟩) (Or.inr ⟨l, hl, rfl⟩) heq
  · exact hsep (j + 1) hnext he

/-- The tree pair the verifier is compared with at step `i` of a level-0 walk is a
`childPair` over an occupied position, when `j` is occupied. -/
lemma treePair_mem (h : Hash) (z0 : UInt256) (L : List UInt256) (height j i : ℕ)
    (hj : j < L.length) (hi : i < height) :
    TreePair h z0 L height (treePair h z0 L (0 + i) (j / 2 ^ i)) := by
  refine Or.inl ⟨i, hi, j / 2 ^ i / 2, ?_, by rw [Nat.zero_add]; rfl⟩
  have hd : j / 2 ^ i / 2 = j / 2 ^ (i + 1) := by
    rw [Nat.div_div_eq_div_mul, show 2 ^ i * 2 = (2 : ℕ) ^ (i + 1) from by ring]
  rw [hd]
  exact lt_of_le_of_lt (Nat.div_mul_le_self j _) hj

/-- **AN ACCEPTED PATH WITH THE CHECK IS THE LAST LEAF, UNDER A BOUNDED PREMISE.** -/
theorem accepted_last_leaf_on (h : Hash) (z0 : UInt256)
    (L : List UInt256) (sibs : ℕ → UInt256) (height j : ℕ) (x : UInt256)
    (hcap : L.length ≤ 2 ^ height) (hj : j < L.length) (hsep : EntriesNotEmpty z0 L)
    (hinj : PairInjOn h (fun p => TreePair h z0 L height p ∨ VerifiedPair h sibs height j x p))
    (haccept : walkPure h sibs 0 height j x = rootOf h z0 L height)
    (hzero : ∀ l < height, (j / 2 ^ l) % 2 = 0 → sibs l = zeros h z0 l) :
    j + 1 = L.length := by
  rcases accepted_last_leaf_or_pinned_break h z0 L sibs height j x hcap hj haccept hzero with
    h1 | hb | ⟨i, hi, hne, heq⟩
  · exact h1
  · exact absurd hb (no_pinned_break_on h z0 L height j hcap hsep
      (pairInjOn_mono hinj (fun p hp => Or.inl hp)))
  · exact absurd (hinj _ _ (Or.inr ⟨i, hi, rfl⟩) (Or.inl (treePair_mem h z0 L height j i hj hi))
      heq) hne

/-- Every pair in the demo instance's bounded set is one of four explicit pairs. -/
lemma demo_pairs_mem (p : UInt256 × UInt256)
    (hp : TreePair demoHash 0 [5, 7] 2 p
      ∨ VerifiedPair demoHash (honestSibs demoHash 0 [5, 7] 1) 2 1 7 p) :
    p ∈ ([(5, 7), (20, 1), (0, 0), (1, 1)] : List (UInt256 × UInt256)) := by
  rcases hp with (⟨l, hl, m, hm, rfl⟩ | ⟨l, hl, rfl⟩) | ⟨i, hi, rfl⟩
  · interval_cases l
    · have : m = 0 := by simp at hm; omega
      subst this; decide
    · have : m = 0 := by simp at hm; omega
      subst this; decide
  · interval_cases l <;> decide
  · interval_cases i <;> decide

/-- The demo instance meets the bounded no-collision premise. -/
theorem demo_pairInjOn : PairInjOn demoHash (fun p => TreePair demoHash 0 [5, 7] 2 p
    ∨ VerifiedPair demoHash (honestSibs demoHash 0 [5, 7] 1) 2 1 7 p) := by
  have hW : ∀ p ∈ ([(5, 7), (20, 1), (0, 0), (1, 1)] : List (UInt256 × UInt256)),
      ∀ q ∈ ([(5, 7), (20, 1), (0, 0), (1, 1)] : List (UInt256 × UInt256)),
        demoHash p.1 p.2 = demoHash q.1 q.2 → p = q := by
    intro p hp q hq he
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp hq
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
      first | rfl | exact absurd he (by decide)
  exact fun p q hp hq he => hW p (demo_pairs_mem p hp) q (demo_pairs_mem q hq) he

theorem demo_entriesNotEmpty : EntriesNotEmpty 0 [5, 7] := by
  intro m hm
  simp only [List.length_cons, List.length_nil] at hm
  interval_cases m <;> decide

theorem demo_collides : ∃ a b c d : UInt256, (a, b) ≠ (c, d) ∧ demoHash a b = demoHash c d :=
  ⟨2, 0, 0, 1, by decide, by decide⟩

theorem accepted_last_leaf_on_satisfiable : Properties.AcceptedLastLeafOnSatisfiable :=
  ⟨demoHash, 0, [5, 7], honestSibs demoHash 0 [5, 7] 1, 2, 1, 7,
    by decide, by decide, demo_entriesNotEmpty,
    pairInjOn_mono demo_pairInjOn (fun p hp => Or.inl hp), demo_pairInjOn,
    by decide, by decide, ⟨1, by decide, by decide⟩, demo_collides⟩

theorem LastLeafOrPinnedBreak : Properties.LastLeafOrPinnedBreak := last_leaf_or_pinned_break
theorem PinnedBreakNotAlways : Properties.PinnedBreakNotAlways := pinned_break_not_always
theorem NoPinnedBreakAtEnd : Properties.NoPinnedBreakAtEnd := no_pinned_break_at_end
theorem AcceptedLastLeafOrPinnedBreak : Properties.AcceptedLastLeafOrPinnedBreak :=
  accepted_last_leaf_or_pinned_break
theorem AcceptedLastLeafOrPinnedBreakSatisfiable :
    Properties.AcceptedLastLeafOrPinnedBreakSatisfiable :=
  accepted_last_leaf_or_pinned_break_satisfiable
theorem AcceptedPinnedConclusionNotAlways : Properties.AcceptedPinnedConclusionNotAlways :=
  accepted_pinned_conclusion_not_always
theorem NoPinnedBreakOn : Properties.NoPinnedBreakOn := no_pinned_break_on
theorem AcceptedLastLeafOn : Properties.AcceptedLastLeafOn := accepted_last_leaf_on
theorem AcceptedLastLeafOnSatisfiable : Properties.AcceptedLastLeafOnSatisfiable :=
  accepted_last_leaf_on_satisfiable

end MerkleSpec.LastLeaf
