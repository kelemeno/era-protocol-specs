import EraSpec.Contracts.ChainBatchRootTree.Properties.Layout
import EraSpec.Contracts.Merkle.Proofs.PathCollision
import EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashPinned

/-!
# Proofs: the chain batch root layout and its depth-3 openings (see `../Specs/Layout.lean`)

The opening argument is one step on top of `MerkleSpec.Verifier.walk_pins_or_collision`. A
3-step walk ends in `node` of the pair it hashed last (`walkPure_succ_eq_walkPair`). If that pair
is not `compute`'s pair `(liveSubtreeNode, RESERVED_SUBTREE_NODE)`, that is the located collision.
If it is, the walk's value after two steps is the left (live half) or right (reserved half) node,
and the lower two levels are the `FullMerkle` tree over `[a, b, c, d]` with padding `0`, where
`walk_pins_or_collision` applies; in the reserved half that needs the reserved node to be the
level-2 zero, which is `ReservedSubtreeDocumented`.
-/

namespace Contracts.ChainBatchRootTree

open MerkleSpec MerkleSpec.Verifier
open AttackVectors.BundleHashEncoding (HashCollision word toBytesBE word_length word_val_inj)

/-! ## Byte-level facts -/

theorem w32_length (x : UInt256) : (w32 x).length = 32 := word_length x.val

theorem nodePre_length (a b : UInt256) : (nodePre a b).length = 64 := by
  simp [nodePre]

theorem pairPre_length (p : UInt256 × UInt256) : (pairPre p).length = 64 := nodePre_length _ _

theorem nodePre_inj {a b c d : UInt256} (h : nodePre a b = nodePre c d) : a = c ∧ b = d := by
  have h1 := List.append_inj h (by rw [w32_length, w32_length])
  exact ⟨word_val_inj h1.1, word_val_inj h1.2⟩

theorem pairPre_inj {p q : UInt256 × UInt256} (h : pairPre p = pairPre q) : p = q := by
  obtain ⟨h1, h2⟩ := nodePre_inj h
  exact Prod.ext h1 h2

/-- A pair collision of `node keccak` is a keccak collision on the two 64-byte node preimages. -/
theorem pair_collision_keccak (keccak : Keccak) {p q : UInt256 × UInt256} (hne : p ≠ q)
    (heq : node keccak p.1 p.2 = node keccak q.1 q.2) :
    HashCollision keccak (pairPre p) (pairPre q) :=
  ⟨fun h => hne (pairPre_inj h), heq⟩

/-! ## Walk facts -/

/-- The pair a walk hashes at step `i` is `walkStep` of its value after `i` steps. -/
theorem walkPair_eq_walkStep (h : Hash) (sibs : ℕ → UInt256) :
    ∀ (i lvl j : ℕ) (x : UInt256),
      walkPair h sibs lvl j x i = walkStep sibs (lvl + i) (j / 2 ^ i) (walkPure h sibs lvl i j x)
  | 0, lvl, j, x => by simp [walkPair]
  | i + 1, lvl, j, x => by
      rw [walkPair_succ, walkPair_eq_walkStep h sibs i (lvl + 1) (j / 2) _, walkPure_succ,
        walkStep_hash h sibs lvl j x, show lvl + 1 + i = lvl + (i + 1) from by omega,
        Nat.div_div_eq_div_mul, ← pow_succ']

/-- A walk reads only the sibling entries at the levels it climbs. -/
theorem walkPure_congr (h : Hash) {s s' : ℕ → UInt256} :
    ∀ (k lvl j : ℕ) (x : UInt256), (∀ l, lvl ≤ l → l < lvl + k → s l = s' l) →
      walkPure h s lvl k j x = walkPure h s' lvl k j x
  | 0, _, _, _, _ => rfl
  | k + 1, lvl, j, x, hs => by
      rw [walkPure_succ, walkPure_succ, hs lvl le_rfl (by omega)]
      exact walkPure_congr h k (lvl + 1) (j / 2) _ (fun l h1 h2 => hs l (by omega) (by omega))

/-- The pair hashed at step `i` reads only the sibling entries at levels up to `lvl + i`. -/
theorem walkPair_congr (h : Hash) {s s' : ℕ → UInt256} (i lvl j : ℕ) (x : UInt256)
    (hs : ∀ l, lvl ≤ l → l ≤ lvl + i → s l = s' l) :
    walkPair h s lvl j x i = walkPair h s' lvl j x i := by
  rw [walkPair_eq_walkStep, walkPair_eq_walkStep,
    walkPure_congr h i lvl j x (fun l h1 h2 => hs l h1 (by omega))]
  unfold walkStep
  rw [hs (lvl + i) (by omega) le_rfl]

/-! ## The four-leaf tree's levels -/

theorem levels_two_live (keccak : Keccak) (a b c d : UInt256) :
    levels (node keccak) 0 (liveLeaves a b c d) 2 = [liveSubtreeNode keccak a b c d] := by
  simp [liveLeaves, liveSubtreeNode]

theorem zeros_two (keccak : Keccak) :
    zeros (node keccak) 0 2 = node keccak (node keccak 0 0) (node keccak 0 0) := by
  simp

/-! ## (a) -/

theorem compute_eq_rootOf (keccak : Keccak) (a b c d : UInt256)
    (hres : ReservedSubtreeDocumented keccak) :
    compute keccak a b c d = rootOf (node keccak) 0 (liveLeaves a b c d) TREE_DEPTH := by
  unfold ReservedSubtreeDocumented at hres
  rw [rootOf_def, TREE_DEPTH, levels_succ, levels_two_live, levelUp_single, zeros_two,
    List.headD_cons, ← hres]
  rfl

/-- A keccak meeting the documented reserved value: it maps 64 zero bytes to `1` and the node
preimage of `(1, 1)` to `RESERVED_SUBTREE_NODE`. -/
def documentedKeccak : Keccak := fun s =>
  if s = nodePre 0 0 then 1 else if s = nodePre 1 1 then RESERVED_SUBTREE_NODE else 0

theorem documentedKeccak_documented : ReservedSubtreeDocumented documentedKeccak := by
  have h01 : nodePre 1 1 ≠ nodePre 0 0 := fun h => absurd (nodePre_inj h).1 (by decide)
  have e1 : node documentedKeccak 0 0 = 1 := by
    show documentedKeccak (nodePre 0 0) = 1
    simp [documentedKeccak]
  have e2 : node documentedKeccak 1 1 = RESERVED_SUBTREE_NODE := by
    show documentedKeccak (nodePre 1 1) = RESERVED_SUBTREE_NODE
    simp [documentedKeccak, h01]
  unfold ReservedSubtreeDocumented
  rw [e1, e2]

/-- A keccak under which `compute` differs from the height-3 fold: `64` zero bytes go to `5`,
everything else to `0`. -/
def offsetKeccak : Keccak := fun s => if s = nodePre 0 0 then 5 else 0

theorem compute_ne_rootOf_offset :
    compute offsetKeccak 0 0 0 0 ≠ rootOf (node offsetKeccak) 0 (liveLeaves 0 0 0 0) TREE_DEPTH := by
  have hres0 : RESERVED_SUBTREE_NODE ≠ 0 := by decide
  have h55 : nodePre 5 5 ≠ nodePre 0 0 := fun h => absurd (nodePre_inj h).1 (by decide)
  have h0R : nodePre 0 RESERVED_SUBTREE_NODE ≠ nodePre 0 0 :=
    fun h => hres0 (nodePre_inj h).2
  have hn00 : node offsetKeccak 0 0 = 5 := by simp [node, offsetKeccak]
  have hn55 : node offsetKeccak 5 5 = 0 := by
    show offsetKeccak (nodePre 5 5) = 0
    simp [offsetKeccak, h55]
  have hlive : liveSubtreeNode offsetKeccak 0 0 0 0 = 0 := by
    simp only [liveSubtreeNode, hn00, hn55]
  have hc : compute offsetKeccak 0 0 0 0 = 0 := by
    show node offsetKeccak (liveSubtreeNode offsetKeccak 0 0 0 0) RESERVED_SUBTREE_NODE = 0
    rw [hlive]
    show offsetKeccak (nodePre 0 RESERVED_SUBTREE_NODE) = 0
    simp [offsetKeccak, h0R]
  have hr : rootOf (node offsetKeccak) 0 (liveLeaves 0 0 0 0) TREE_DEPTH = 5 := by
    rw [rootOf_def, TREE_DEPTH, levels_succ, levels_two_live, levelUp_single, zeros_two,
      List.headD_cons, hlive, hn00, hn55, hn00]
  rw [hc, hr]
  decide

/-! ## (b) The core opening argument -/

/-- The top step of a depth-3 walk: the walk's value is `node` of the pair it hashed at level 2,
and that pair is `(v₂, sibs 2)` in the live half and `(sibs 2, v₂)` in the reserved half. -/
theorem top_pair (keccak : Keccak) (sibs : ℕ → UInt256) (j : ℕ) (x : UInt256) :
    walkPure (node keccak) sibs 0 TREE_DEPTH j x
        = node keccak (walkPair (node keccak) sibs 0 j x 2).1 (walkPair (node keccak) sibs 0 j x 2).2
      ∧ walkPair (node keccak) sibs 0 j x 2
        = walkStep sibs 2 (j / 4) (walkPure (node keccak) sibs 0 2 j x) := by
  refine ⟨walkPure_succ_eq_walkPair (node keccak) sibs 2 0 j x, ?_⟩
  rw [walkPair_eq_walkStep]
  rfl

/-- Lift a `PathCollision` on the two lower levels to an `OpeningCollision`. -/
theorem openingCollision_of_pathCollision (keccak : Keccak) (a b c d : UInt256)
    (sibs : ℕ → UInt256) (j : ℕ) (x : UInt256)
    (hc : PathCollision (node keccak) 0 (liveLeaves a b c d) sibs 0 2 j x) :
    OpeningCollision keccak a b c d sibs j x := by
  obtain ⟨i, hi, hne, heq⟩ := hc
  have hpair : cbrPair keccak a b c d i j
      = treePair (node keccak) 0 (liveLeaves a b c d) (0 + i) (j / 2 ^ i) := by
    simp [cbrPair, hi]
  refine ⟨i, by omega, ?_⟩
  rw [hpair]
  exact pair_collision_keccak keccak hne heq

/-- **THE CORE.** A depth-3 walk reaching `compute a b c d` at index `j < 4`, or at `j < 8` under
the documented reserved value, opens `[a, b, c, d].getD j 0` or locates an `OpeningCollision`. -/
theorem opening_core (keccak : Keccak) (a b c d : UInt256) (sibs : ℕ → UInt256) (j : ℕ)
    (x : UInt256) (hj : j < 4 ∨ (ReservedSubtreeDocumented keccak ∧ j < 8))
    (hw : walkPure (node keccak) sibs 0 TREE_DEPTH j x = compute keccak a b c d) :
    x = (liveLeaves a b c d).getD j 0 ∨ OpeningCollision keccak a b c d sibs j x := by
  obtain ⟨htop, hstep⟩ := top_pair keccak sibs j x
  set p := walkPair (node keccak) sibs 0 j x 2 with hp
  have hcbr2 : cbrPair keccak a b c d 2 j
      = (liveSubtreeNode keccak a b c d, RESERVED_SUBTREE_NODE) := by
    simp [cbrPair]
  by_cases hpe : p = (liveSubtreeNode keccak a b c d, RESERVED_SUBTREE_NODE)
  · -- The walk hashed `compute`'s own top pair: its value after two steps is a level-2 node.
    have hv2 : walkPure (node keccak) sibs 0 2 j x
        = (levels (node keccak) 0 (liveLeaves a b c d) (0 + 2)).getD (j / 2 ^ 2)
            (zeros (node keccak) 0 (0 + 2)) := by
      rw [Nat.zero_add, levels_two_live, zeros_two]
      rcases hj with hj | ⟨hres, hj⟩
      · have hq : j / 4 = 0 := Nat.div_eq_of_lt hj
        rw [hstep, hq] at hpe
        simp only [walkStep, Nat.zero_mod, zero_ne_one, ite_false, Prod.mk.injEq] at hpe
        rw [show j / 2 ^ 2 = 0 from hq]
        exact hpe.1
      · by_cases hlow : j < 4
        · have hq : j / 4 = 0 := Nat.div_eq_of_lt hlow
          rw [hstep, hq] at hpe
          simp only [walkStep, Nat.zero_mod, zero_ne_one, ite_false, Prod.mk.injEq] at hpe
          rw [show j / 2 ^ 2 = 0 from hq]
          exact hpe.1
        · have hq : j / 4 = 1 := by omega
          rw [hstep, hq] at hpe
          simp only [walkStep, Nat.one_mod, ite_true, Prod.mk.injEq] at hpe
          rw [show j / 2 ^ 2 = 1 from hq]
          unfold ReservedSubtreeDocumented at hres
          rw [hpe.2, hres]
          rfl
    rcases walk_pins_or_collision (node keccak) 0 (liveLeaves a b c d) sibs 2 0 j x hv2 with
      ⟨hx, _⟩ | hc
    · left
      simpa using hx.symm
    · right
      exact openingCollision_of_pathCollision keccak a b c d sibs j x hc
  · -- The walk hashed a different top pair: that is the collision, at level 2.
    right
    refine ⟨2, by omega, ?_⟩
    rw [hcbr2]
    refine pair_collision_keccak keccak hpe ?_
    rw [← htop, hw]
    rfl

theorem live_leaf_opening (keccak : Keccak) (a b c d : UInt256) (sibs : ℕ → UInt256) (j : ℕ)
    (x : UInt256) (hj : j < 4)
    (hw : walkPure (node keccak) sibs 0 TREE_DEPTH j x = compute keccak a b c d) :
    x = (liveLeaves a b c d).getD j 0 ∨ OpeningCollision keccak a b c d sibs j x :=
  opening_core keccak a b c d sibs j x (Or.inl hj) hw

theorem reserved_leaf_opening (keccak : Keccak) (a b c d : UInt256) (sibs : ℕ → UInt256)
    (j : ℕ) (x : UInt256) (hres : ReservedSubtreeDocumented keccak) (hj4 : 4 ≤ j)
    (hj8 : j < 2 ^ TREE_DEPTH)
    (hw : walkPure (node keccak) sibs 0 TREE_DEPTH j x = compute keccak a b c d) :
    x = 0 ∨ OpeningCollision keccak a b c d sibs j x := by
  have hj8' : j < 8 := by simpa [TREE_DEPTH] using hj8
  rcases opening_core keccak a b c d sibs j x (Or.inr ⟨hres, hj8'⟩) hw with h | h
  · left
    rw [h]
    exact getD_default _ _ _ (by simp [liveLeaves]; omega)
  · exact Or.inr h

theorem opening_pins (keccak : Keccak) (a b c d : UInt256) (sibs : ℕ → UInt256) (j : ℕ)
    (x : UInt256) (hres : ReservedSubtreeDocumented keccak) (hj : j < 2 ^ TREE_DEPTH)
    (hw : walkPure (node keccak) sibs 0 TREE_DEPTH j x = compute keccak a b c d) :
    x = (liveLeaves a b c d).getD j 0 ∨ OpeningCollision keccak a b c d sibs j x :=
  opening_core keccak a b c d sibs j x (Or.inr ⟨hres, by simpa [TREE_DEPTH] using hj⟩) hw

theorem imt_root_hop_pins (keccak : Keccak) (a b c d : UInt256) (sibs : ℕ → UInt256) (len : ℕ)
    (x : UInt256) :
    (ImtRootHopAccepted keccak a b c d sibs len IMT_BEGIN_ROOT_LEAF_INDEX x →
        x = c ∨ OpeningCollision keccak a b c d sibs IMT_BEGIN_ROOT_LEAF_INDEX x)
      ∧ (ImtRootHopAccepted keccak a b c d sibs len IMT_END_ROOT_LEAF_INDEX x →
        x = d ∨ OpeningCollision keccak a b c d sibs IMT_END_ROOT_LEAF_INDEX x) := by
  constructor
  · intro hacc
    have hw := hacc.reachesBatchRoot
    rw [hacc.depthPinned] at hw
    simpa [liveLeaves, IMT_BEGIN_ROOT_LEAF_INDEX] using
      live_leaf_opening keccak a b c d sibs IMT_BEGIN_ROOT_LEAF_INDEX x (by decide) hw
  · intro hacc
    have hw := hacc.reachesBatchRoot
    rw [hacc.depthPinned] at hw
    simpa [liveLeaves, IMT_END_ROOT_LEAF_INDEX] using
      live_leaf_opening keccak a b c d sibs IMT_END_ROOT_LEAF_INDEX x (by decide) hw

theorem imt_root_hop_depth_pin_needed (keccak : Keccak) (a b c d : UInt256)
    (hres : ReservedSubtreeDocumented keccak) (m : ℕ)
    (hm : m = IMT_BEGIN_ROOT_LEAF_INDEX ∨ m = IMT_END_ROOT_LEAF_INDEX) :
    m < 2 ^ 2
      ∧ walkPure (node keccak)
          (fun l => if l = 0 then node keccak 0 0 else liveSubtreeNode keccak a b c d) 0 2 m
          (node keccak 0 0) = compute keccak a b c d := by
  unfold ReservedSubtreeDocumented at hres
  rcases hm with rfl | rfl
  · refine ⟨by decide, ?_⟩
    simp only [IMT_BEGIN_ROOT_LEAF_INDEX, walkPure_succ, walkPure_zero]
    norm_num
    rw [← hres]
    rfl
  · refine ⟨by decide, ?_⟩
    simp only [IMT_END_ROOT_LEAF_INDEX, walkPure_succ, walkPure_zero]
    norm_num
    rw [← hres]
    rfl

/-! ## Non-triviality -/

/-- The opening siblings agree with the `FullMerkle` honest siblings on the two lower levels. -/
theorem openingSibs_low (keccak : Keccak) (a b c d : UInt256) (j l : ℕ) (hl : l < 2) :
    openingSibs keccak a b c d j l = honestSibs (node keccak) 0 (liveLeaves a b c d) j l := by
  simp [openingSibs, hl]

/-- The honest walk's value after two steps is the level-2 node above `j`. -/
theorem honest_two_steps (keccak : Keccak) (a b c d : UInt256) (j : ℕ) :
    walkPure (node keccak) (openingSibs keccak a b c d j) 0 2 j ((liveLeaves a b c d).getD j 0)
      = (levels (node keccak) 0 (liveLeaves a b c d) 2).getD (j / 2 ^ 2)
          (zeros (node keccak) 0 2) := by
  rw [walkPure_congr (node keccak) 2 0 j _
    (fun l _ h2 => openingSibs_low keccak a b c d j l (by omega))]
  have := walkPure_levels_all (node keccak) 0 (honestSibs (node keccak) 0 (liveLeaves a b c d) j)
    (liveLeaves a b c d) 2 0 j (fun l _ _ => by simp [honestSibs])
  simpa using this

theorem honest_opening_accepted (keccak : Keccak) (a b c d : UInt256) (j : ℕ)
    (hj : j < 4 ∨ (ReservedSubtreeDocumented keccak ∧ j < 2 ^ TREE_DEPTH)) :
    walkPure (node keccak) (openingSibs keccak a b c d j) 0 TREE_DEPTH j
      ((liveLeaves a b c d).getD j 0) = compute keccak a b c d := by
  rw [TREE_DEPTH, walkPure_add (node keccak) _ 2 1 0 j, honest_two_steps, levels_two_live,
    zeros_two, walkPure_succ, walkPure_zero]
  by_cases hlow : j < 4
  · have hq : j / 2 ^ 2 = 0 := Nat.div_eq_of_lt (by simpa using hlow)
    rw [hq]
    simp [openingSibs, hlow, compute]
  · rcases hj with hj | ⟨hres, hj⟩
    · exact absurd hj hlow
    · have hq : j / 2 ^ 2 = 1 := by simp [TREE_DEPTH] at hj; omega
      rw [hq]
      unfold ReservedSubtreeDocumented at hres
      simp [openingSibs, hlow, compute, ← hres]

theorem honest_opening_no_collision (keccak : Keccak) (a b c d : UInt256) (j : ℕ)
    (hj : j < 4 ∨ (ReservedSubtreeDocumented keccak ∧ j < 2 ^ TREE_DEPTH)) :
    ¬ OpeningCollision keccak a b c d (openingSibs keccak a b c d j) j
      ((liveLeaves a b c d).getD j 0) := by
  rintro ⟨i, hi, hne, _⟩
  apply hne
  congr 1
  by_cases hi2 : i < 2
  · -- The two lower levels: the honest `FullMerkle` walk hashes the tree's pairs.
    have hcongr := walkPair_congr (node keccak) (s := openingSibs keccak a b c d j)
      (s' := honestSibs (node keccak) 0 (liveLeaves a b c d) j) i 0 j
      ((liveLeaves a b c d).getD j 0)
      (fun l _ h2 => openingSibs_low keccak a b c d j l (by omega))
    rw [hcongr, walkPair_honest (node keccak) 0 (liveLeaves a b c d) _ i 0 j _
      (fun l _ _ => by simp [honestSibs]) (by simp)]
    simp [cbrPair, hi2]
  · -- The top level: the walk hashes `(liveSubtreeNode, RESERVED_SUBTREE_NODE)`.
    have hi2' : i = 2 := by omega
    subst hi2'
    rw [(top_pair keccak _ j _).2, honest_two_steps, levels_two_live, zeros_two]
    simp only [cbrPair, show ¬ (2 < 2) from by omega, ite_false]
    by_cases hlow : j < 4
    · have hq : j / 4 = 0 := Nat.div_eq_of_lt hlow
      rw [hq, show j / 2 ^ 2 = 0 from hq]
      simp [walkStep, openingSibs, hlow]
    · rcases hj with hj | ⟨hres, hj⟩
      · exact absurd hj hlow
      · have hq : j / 4 = 1 := by simp [TREE_DEPTH] at hj; omega
        rw [hq, show j / 2 ^ 2 = 1 from hq]
        unfold ReservedSubtreeDocumented at hres
        simp [walkStep, openingSibs, hlow, ← hres]

/-- On the constant keccak every node is `0`, so every walk reaches `compute`. -/
theorem constant_keccak_walk (sibs : ℕ → UInt256) (j : ℕ) (x : UInt256) :
    walkPure (node (fun _ => 0)) sibs 0 TREE_DEPTH j x = compute (fun _ => 0) 0 0 0 0 := by
  show walkPure (node (fun _ => 0)) sibs 0 (2 + 1) j x = _
  rw [walkPure_succ_eq_walkPair (node (fun _ => 0)) sibs 2 0 j x]
  rfl

theorem opening_collision_fires : Properties.OpeningCollisionFires := by
  refine ⟨fun _ => 0, 0, 0, 0, 0, fun _ => 0, 0, 1, by decide, constant_keccak_walk _ _ _,
    by simp [liveLeaves], 0, by decide, ?_, rfl⟩
  intro h
  have := (nodePre_inj h).1
  simp [walkPair, walkStep, cbrPair, treePair, liveLeaves] at this

/-! ## (e) Leaf 1 of the genesis root -/

theorem genesis_leaf_one (keccak : Keccak) (sibs : ℕ → UInt256) (x : UInt256)
    (hw : walkPure (node keccak) sibs 0 TREE_DEPTH MULTICHAIN_ROOT_LEAF_INDEX x
        = genesisChainBatchRoot keccak) :
    x = 0 ∨ OpeningCollision keccak 0 0 EMPTY_IMT_ROOT EMPTY_IMT_ROOT sibs
      MULTICHAIN_ROOT_LEAF_INDEX x := by
  simpa [liveLeaves, MULTICHAIN_ROOT_LEAF_INDEX] using
    live_leaf_opening keccak 0 0 EMPTY_IMT_ROOT EMPTY_IMT_ROOT sibs MULTICHAIN_ROOT_LEAF_INDEX x
      (by decide) hw

theorem genesis_leaf_one_not_initial (keccak : Keccak) (padC chainId : UInt256)
    (sibs : ℕ → UInt256)
    (hw : walkPure (node keccak) sibs 0 TREE_DEPTH MULTICHAIN_ROOT_LEAF_INDEX
        (initialAggregatedRoot keccak padC chainId) = genesisChainBatchRoot keccak) :
    keccak (chainIdLeafPre padC 0 chainId) = 0
      ∨ OpeningCollision keccak 0 0 EMPTY_IMT_ROOT EMPTY_IMT_ROOT sibs MULTICHAIN_ROOT_LEAF_INDEX
          (initialAggregatedRoot keccak padC chainId) :=
  genesis_leaf_one keccak sibs _ hw

/-! ### The witness keccak for leaf 1

`genesisKeccak` gives the four node preimages of the genesis tree unique values `1 … 4`, every
96-byte string the value `5`, and everything else `0`. Under it the genesis root is `4`, and a
depth-3 walk at leaf 1 reaching it must hash exactly the tree's pairs, so its claimed leaf is `0`. -/

/-- The four node preimages of the genesis tree. -/
def genesisPre₁ : List UInt8 := nodePre 0 0
def genesisPre₂ : List UInt8 := nodePre EMPTY_IMT_ROOT EMPTY_IMT_ROOT
def genesisPre₃ : List UInt8 := nodePre 1 2
def genesisPre₄ : List UInt8 := nodePre 3 RESERVED_SUBTREE_NODE

/-- The witness keccak. -/
def genesisKeccak : Keccak := fun s =>
  if s = genesisPre₁ then 1 else if s = genesisPre₂ then 2 else if s = genesisPre₃ then 3
  else if s = genesisPre₄ then 4 else if s.length = 96 then 5 else 0

theorem genesisKeccak_genesis : genesisChainBatchRoot genesisKeccak = 4 := by
  have h12 : genesisPre₂ ≠ genesisPre₁ := fun h => by
    have := (nodePre_inj h).1; revert this; decide
  have h13 : genesisPre₃ ≠ genesisPre₁ := fun h => by
    have := (nodePre_inj h).1; revert this; decide
  have h23 : genesisPre₃ ≠ genesisPre₂ := fun h => by
    have := (nodePre_inj h).1; revert this; decide
  have h14 : genesisPre₄ ≠ genesisPre₁ := fun h => by
    have := (nodePre_inj h).1; revert this; decide
  have h24 : genesisPre₄ ≠ genesisPre₂ := fun h => by
    have := (nodePre_inj h).1; revert this; decide
  have h34 : genesisPre₄ ≠ genesisPre₃ := fun h => by
    have := (nodePre_inj h).1; revert this; decide
  have e1 : node genesisKeccak 0 0 = 1 := by
    show genesisKeccak genesisPre₁ = 1; simp [genesisKeccak]
  have e2 : node genesisKeccak EMPTY_IMT_ROOT EMPTY_IMT_ROOT = 2 := by
    show genesisKeccak genesisPre₂ = 2; simp [genesisKeccak, h12]
  have e3 : node genesisKeccak 1 2 = 3 := by
    show genesisKeccak genesisPre₃ = 3; simp [genesisKeccak, h13, h23]
  have e4 : node genesisKeccak 3 RESERVED_SUBTREE_NODE = 4 := by
    show genesisKeccak genesisPre₄ = 4; simp [genesisKeccak, h14, h24, h34]
  show node genesisKeccak (node genesisKeccak (node genesisKeccak 0 0)
    (node genesisKeccak EMPTY_IMT_ROOT EMPTY_IMT_ROOT)) RESERVED_SUBTREE_NODE = 4
  rw [e1, e2, e3, e4]

/-- Under `genesisKeccak`, a value in `1 … 4` has exactly one keccak preimage. -/
theorem genesisKeccak_eq_four {s : List UInt8} (h : genesisKeccak s = 4) : s = genesisPre₄ := by
  unfold genesisKeccak at h
  split_ifs at h <;> first | assumption | (exfalso; revert h; decide)

theorem genesisKeccak_eq_three {s : List UInt8} (h : genesisKeccak s = 3) : s = genesisPre₃ := by
  unfold genesisKeccak at h
  split_ifs at h <;> first | assumption | (exfalso; revert h; decide)

theorem genesisKeccak_eq_one {s : List UInt8} (h : genesisKeccak s = 1) : s = genesisPre₁ := by
  unfold genesisKeccak at h
  split_ifs at h <;> first | assumption | (exfalso; revert h; decide)

theorem chainIdLeafPre_length (padC r c : UInt256) : (chainIdLeafPre padC r c).length = 96 := by
  simp [chainIdLeafPre]

theorem genesis_leaf_one_rejects_witness :
    Properties.GenesisLeafOneRejectsInitialAggregatedRootWitness := by
  refine ⟨genesisKeccak, 1, 324, ?_, ?_⟩
  · -- the 96-byte preimage is none of the four 64-byte ones
    have hl := chainIdLeafPre_length 1 0 324
    have hne : ∀ (p q : UInt256), chainIdLeafPre 1 0 324 ≠ nodePre p q := fun p q h => by
      have := congrArg List.length h
      rw [hl, nodePre_length] at this
      omega
    simp only [genesisKeccak, genesisPre₁, genesisPre₂, genesisPre₃, genesisPre₄, hne,
      ite_false, hl, ite_true]
    decide
  · intro sibs hw
    have hagg : initialAggregatedRoot genesisKeccak 1 324 = 5 := by
      have hl := chainIdLeafPre_length 1 0 324
      have hne : ∀ (p q : UInt256), chainIdLeafPre 1 0 324 ≠ nodePre p q := fun p q h => by
        have := congrArg List.length h
        rw [hl, nodePre_length] at this
        omega
      simp only [initialAggregatedRoot, genesisKeccak, genesisPre₁, genesisPre₂, genesisPre₃,
        genesisPre₄, hne, ite_false, hl, ite_true]
    rw [hagg, genesisKeccak_genesis] at hw
    -- Top step: the pair hashed at level 2 is `(3, RESERVED_SUBTREE_NODE)`.
    obtain ⟨htop, hstep⟩ := top_pair genesisKeccak sibs MULTICHAIN_ROOT_LEAF_INDEX 5
    rw [htop] at hw
    have h4 := genesisKeccak_eq_four hw
    have hp2 := pairPre_inj (p := walkPair (node genesisKeccak) sibs 0 MULTICHAIN_ROOT_LEAF_INDEX 5 2)
      (q := (3, RESERVED_SUBTREE_NODE)) h4
    rw [hstep] at hp2
    simp only [MULTICHAIN_ROOT_LEAF_INDEX, walkStep, show (1 : ℕ) / 4 = 0 from rfl, Nat.zero_mod,
      zero_ne_one, ite_false, Prod.mk.injEq] at hp2
    -- Level 1: the walk's value after two steps is `3`, so it hashed `(1, 2)`.
    have hv2 := hp2.1
    rw [walkPure_succ_eq_walkPair (node genesisKeccak) sibs 1 0 1 5] at hv2
    have h3 := genesisKeccak_eq_three hv2
    have hp1 := pairPre_inj (p := walkPair (node genesisKeccak) sibs 0 1 5 1) (q := (1, 2)) h3
    rw [walkPair_eq_walkStep] at hp1
    simp only [walkStep, show (1 : ℕ) / 2 ^ 1 = 0 from rfl, Nat.zero_mod, zero_ne_one, ite_false,
      Prod.mk.injEq] at hp1
    -- Level 0: the walk's value after one step is `1`, so it hashed `(0, 0)`, and its leaf is `0`.
    have hv1 := hp1.1
    rw [walkPure_succ_eq_walkPair (node genesisKeccak) sibs 0 0 1 5] at hv1
    have h1 := genesisKeccak_eq_one hv1
    have hp0 := pairPre_inj (p := walkPair (node genesisKeccak) sibs 0 1 5 0) (q := (0, 0)) h1
    simp only [walkPair, walkStep, Nat.one_mod, ite_true, Prod.mk.injEq] at hp0
    exact absurd hp0.2 (by decide)

/-! ## Certificates -/

theorem ComputeIsRootOfHeightThree : Properties.ComputeIsRootOfHeightThree :=
  fun keccak a b c d hres => compute_eq_rootOf keccak a b c d hres

theorem ComputeRootNeedsDocumentedValue : Properties.ComputeRootNeedsDocumentedValue :=
  ⟨⟨documentedKeccak, documentedKeccak_documented⟩, offsetKeccak, 0, 0, 0, 0,
    compute_ne_rootOf_offset⟩

theorem LiveLeafOpeningPinsLeafOrCollision : Properties.LiveLeafOpeningPinsLeafOrCollision :=
  live_leaf_opening

theorem ReservedLeafOpeningPinsZeroOrCollision :
    Properties.ReservedLeafOpeningPinsZeroOrCollision :=
  reserved_leaf_opening

theorem OpeningPinsLeafOrCollision : Properties.OpeningPinsLeafOrCollision := opening_pins

theorem ImtRootHopPinsLeafOrCollision : Properties.ImtRootHopPinsLeafOrCollision :=
  imt_root_hop_pins

theorem ImtRootHopDepthPinNeeded : Properties.ImtRootHopDepthPinNeeded :=
  imt_root_hop_depth_pin_needed

theorem HonestOpeningAccepted : Properties.HonestOpeningAccepted := honest_opening_accepted

theorem HonestOpeningNoCollision : Properties.HonestOpeningNoCollision :=
  honest_opening_no_collision

theorem OpeningCollisionFires : Properties.OpeningCollisionFires := opening_collision_fires

theorem GenesisLeafOneOpensZeroOrCollision : Properties.GenesisLeafOneOpensZeroOrCollision :=
  genesis_leaf_one

theorem GenesisLeafOneNotInitialAggregatedRoot :
    Properties.GenesisLeafOneNotInitialAggregatedRoot :=
  genesis_leaf_one_not_initial

theorem GenesisLeafOneRejectsInitialAggregatedRootWitness :
    Properties.GenesisLeafOneRejectsInitialAggregatedRootWitness :=
  genesis_leaf_one_rejects_witness

theorem ReservedOpeningWitness : Properties.ReservedOpeningWitness :=
  ⟨documentedKeccak, documentedKeccak_documented, fun a b c d j hj =>
    ⟨honest_opening_accepted documentedKeccak a b c d j (Or.inr ⟨documentedKeccak_documented, hj⟩),
     honest_opening_no_collision documentedKeccak a b c d j
       (Or.inr ⟨documentedKeccak_documented, hj⟩)⟩⟩

theorem ImtRootHopWitness : Properties.ImtRootHopWitness := fun keccak a b c d =>
  ⟨⟨rfl, by decide, honest_opening_accepted keccak a b c d 2 (Or.inl (by decide))⟩,
   ⟨rfl, by decide, honest_opening_accepted keccak a b c d 3 (Or.inl (by decide))⟩⟩

end Contracts.ChainBatchRootTree
