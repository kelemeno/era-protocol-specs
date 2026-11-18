import EraSpec.Contracts.DynamicIncrementalMerkle.Properties.ChainTreeBacking
import EraSpec.Contracts.DynamicIncrementalMerkle.Proofs.Model
import EraSpec.Contracts.AtomicInteropProof.Proofs.LastLeaf
import EraSpec.Contracts.AtomicInteropProof.Proofs.LastLeafFaithful
import EraSpec.Contracts.Merkle.Proofs.PathCollision
import EraSpec.Protocol.InteropAtomicity.Proofs.Timeout

/-!
# Proofs: DIM chain trees instantiate `Timeout.RootBacking`, and the last-leaf check

Proofs of `EraSpec.Contracts.DynamicIncrementalMerkle.Properties.ChainTreeBacking`.

The storage side is `Proofs/Model.lean`: every run represents its leaves at `dimHeight`, and
`root()` reads the fold there (`run_represents`, `root_is_fold`, `run_root_is_fold`).  The path
side is the existing honest-walk and last-leaf theory: `honest_walk_root` (the honest path
recomputes the fold), `last_leaf_or_pinned_break` and `no_pinned_break_on` (the zero check
identifies the last leaf, or a pinned break, which the bounded premise rules out), and
`accepted_last_leaf_any_length_or_break` (the deployed acceptance, any length and mask).  The one
new fact is that the last leaf's honest sibling at a left turn is padding
(`last_sibling_is_zero`): its index is past the end of that level, whose width is
`(n - 1) / 2^l + 1` (`levels_length`).

The witnesses evaluate concrete folds symbolically, for every hash, except the path collision,
which is evaluated under `demoHash`.
-/

namespace Contracts.DynamicIncrementalMerkle

open MerkleSpec MerkleSpec.Verifier MerkleSpec.LastLeaf MerkleSpec.LastLeafFaithful
  Contracts.Timeout

/-! ## The last leaf's honest path -/

/-- At a level where the last leaf's path turns left, its honest sibling is past the end of the
level, so it reads as that level's zero. -/
theorem last_sibling_is_zero (h : Hash) (ze : UInt256) (L : List UInt256) (hne : L ≠ [])
    (l : ℕ) (hl : ((L.length - 1) / 2 ^ l) % 2 = 0) :
    honestSibs h ze L (L.length - 1) l = zeros h ze l := by
  have hn : L.length ≠ 0 := by simpa [List.length_eq_zero_iff] using hne
  unfold honestSibs
  rw [show sibIdx ((L.length - 1) / 2 ^ l) = (L.length - 1) / 2 ^ l + 1 from by
      simp [sibIdx, hl]]
  exact getD_default _ _ _ (by rw [levels_length h ze L hn l])

theorem zero_right_side_last (h : Hash) (ze : UInt256) (L : List UInt256) (H : ℕ)
    (hne : L ≠ []) : ZeroRightSide h ze L H (L.length - 1) :=
  fun l _ hl => last_sibling_is_zero h ze L hne l hl

theorem contract_path_last_has_zero_right_side (h : Hash) (ze : UInt256) (L : List UInt256)
    (H : ℕ) (S : PushTree) (hR : Represents h ze L H S) (hne : L ≠ []) :
    root S = some (rootOf h ze L H)
      ∧ walkPure h (honestSibs h ze L (L.length - 1)) 0 H (L.length - 1)
          (L.getD (L.length - 1) ze) = rootOf h ze L H
      ∧ ZeroRightSide h ze L H (L.length - 1) := by
  have hn : L.length ≠ 0 := by simpa [List.length_eq_zero_iff] using hne
  have hcap := hR.capacity
  refine ⟨?_, honest_walk_root h ze L H (L.length - 1) (by omega),
    zero_right_side_last h ze L H hne⟩
  rw [(root_is_fold h ze L H S hR).1, dimRoot, ite_eq_right hne]

theorem contract_path_zero_right_side_is_last_or_pinned_break (h : Hash) (ze : UInt256)
    (L : List UInt256) (H i : ℕ) (hcap : L.length ≤ 2 ^ H) (hi : i < L.length)
    (hz : ZeroRightSide h ze L H i) :
    i + 1 = L.length ∨ PinnedBreak h ze L i :=
  last_leaf_or_pinned_break h ze L (honestSibs h ze L i) H i hcap hi
    (fun _ _ => rfl) (fun l hl hb => hz l hl hb)

theorem contract_path_last_iff (h : Hash) (ze : UInt256) (L : List UInt256) (H i : ℕ)
    (hcap : L.length ≤ 2 ^ H) (hi : i < L.length) (hsep : EntriesNotEmpty ze L)
    (hinj : PairInjOn h (TreePair h ze L H)) :
    ZeroRightSide h ze L H i ↔ i + 1 = L.length := by
  constructor
  · intro hz
    rcases contract_path_zero_right_side_is_last_or_pinned_break h ze L H i hcap hi hz with
      hlast | hb
    · exact hlast
    · exact absurd hb (no_pinned_break_on h ze L H i hcap hsep hinj)
  · intro hlast
    have hne : L ≠ [] := by
      intro he; rw [he] at hi; simp at hi
    rw [show i = L.length - 1 from by omega]
    exact zero_right_side_last h ze L H hne

/-! ## The backing -/

theorem chain_tree_backing_is_stored (h : Hash) (ze : UInt256) (T : ChainTrees h ze)
    (created : ℕ) (c : Contracts.Atomicity.Chain) :
    (T.backing created).leaves c = T.leaves c
      ∧ (T.backing created).height c = dimHeight (T.leaves c).length
      ∧ (T.slRoot created).upTo c + 1 = (T.leaves c).length
      ∧ root (T.state c)
          = some (rootOf h ze ((T.backing created).leaves c) ((T.backing created).height c)) := by
  refine ⟨rfl, rfl, ((T.backing created).upToLast c).symm, ?_⟩
  rw [run_root_is_fold h ze _ _ (T.run c), dimRoot, ite_eq_right (T.nonempty c)]
  rfl

theorem dim_last_batch_accepted (h : Hash) (ze : UInt256) (T : ChainTrees h ze) (created : ℕ)
    (c : Contracts.Atomicity.Chain) :
    LastBatchAccepted (T.backing created) c ((T.slRoot created).upTo c)
      (honestSibs h ze (T.leaves c) ((T.slRoot created).upTo c))
      ((T.leaves c).getD ((T.slRoot created).upTo c) ze) := by
  have hne := T.nonempty c
  have hn : (T.leaves c).length ≠ 0 := by simpa [List.length_eq_zero_iff] using hne
  have hcap := (T.backing created).capacity c
  have hup : (T.slRoot created).upTo c = (T.leaves c).length - 1 := rfl
  refine { inRange := ?_, authenticated := ?_, zeroRightSiblings := ?_ }
  · show (T.slRoot created).upTo c < (T.leaves c).length
    rw [hup]; omega
  · show walkPure h _ 0 (dimHeight (T.leaves c).length) _ _
      = rootOf h ze (T.leaves c) (dimHeight (T.leaves c).length)
    have hc : (T.leaves c).length ≤ 2 ^ dimHeight (T.leaves c).length := hcap
    rw [hup]
    exact honest_walk_root h ze _ _ _ (by omega)
  · intro l _ hl
    rw [hup] at hl ⊢
    exact last_sibling_is_zero h ze (T.leaves c) hne l hl

/-- Storage for any leaf list, from `setup(ze)`. -/
private lemma run_of_list (h : Hash) (ze : UInt256) (L : List UInt256) :
    ∃ S : PushTree, Run h ze L S := by
  obtain ⟨S, _, hS⟩ := push_all_succeeds h ze L
  exact ⟨S, hS⟩

/-- The chain trees in which every chain has pushed `L`. -/
private noncomputable def constTrees (h : Hash) (ze : UInt256) (L : List UInt256) (hL : L ≠ []) :
    ChainTrees h ze where
  leaves := fun _ => L
  state := fun _ => Classical.choose (run_of_list h ze L)
  run := fun _ => Classical.choose_spec (run_of_list h ze L)
  nonempty := fun _ => hL

theorem chain_trees_exist (h : Hash) (ze : UInt256) (L : List UInt256) (hL : L ≠ []) :
    ∃ T : ChainTrees h ze, ∀ c, T.leaves c = L :=
  ⟨constTrees h ze L hL, fun _ => rfl⟩

theorem dim_last_batch_accepted_three_leaves (h : Hash) (ze a b c : UInt256) :
    ∃ T : ChainTrees h ze, ∀ (created : ℕ) (ch : Contracts.Atomicity.Chain),
      T.leaves ch = [a, b, c] ∧ (T.backing created).height ch = 2
        ∧ (T.slRoot created).upTo ch = 2 ∧ (2 / 2 ^ 0) % 2 = 0
        ∧ honestSibs h ze [a, b, c] 2 0 = ze
        ∧ LastBatchAccepted (T.backing created) ch 2 (honestSibs h ze [a, b, c] 2) c := by
  obtain ⟨T, hT⟩ := chain_trees_exist h ze [a, b, c] (by simp)
  refine ⟨T, fun created ch => ?_⟩
  have hacc := dim_last_batch_accepted h ze T created ch
  have hup : (T.slRoot created).upTo ch = 2 := by
    show (T.leaves ch).length - 1 = 2
    rw [hT ch]; rfl
  have hheight : (T.backing created).height ch = 2 := by
    show dimHeight (T.leaves ch).length = 2
    rw [hT ch]; exact dimHeight_three
  rw [hup, hT ch] at hacc
  refine ⟨hT ch, hheight, hup, by norm_num, ?_, hacc⟩
  have := last_sibling_is_zero h ze [a, b, c] (by simp) 0 (by norm_num)
  simpa using this

theorem dim_last_batch_proof_identifies_last_batch_pinned (h : Hash) (ze : UInt256)
    (T : ChainTrees h ze) (created : ℕ) (c : Contracts.Atomicity.Chain) (N : ℕ)
    (sibs : ℕ → UInt256) (x : UInt256) (hacc : LastBatchAccepted (T.backing created) c N sibs x) :
    N + 1 = (T.leaves c).length ∨ PinnedBreak h ze (T.leaves c) N
      ∨ PathCollision h ze (T.leaves c) sibs 0 (dimHeight (T.leaves c).length) N x := by
  rcases Contracts.Timeout.LastBatchProofIdentifiesLastBatchPinned h ze _ (T.backing created) c N
      sibs x hacc with hN | hb | hc
  · left
    rw [hN]
    exact (T.backing created).upToLast c |>.symm
  · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr hc)

/-! ## What the deployed check accepts against DIM storage -/

theorem dim_accepted_last_leaf_any_length_or_break (h : Hash) (ze : UInt256) (L : List UInt256)
    (S : PushTree) (sibs : ℕ → UInt256) (k j : ℕ) (x r : UInt256) (hrun : Run h ze L S)
    (hne : L ≠ []) (hroot : root S = some r) (hj : j < 2 ^ k)
    (hw : walkPure h sibs 0 k j x = r)
    (hz : ∀ l < k, (j / 2 ^ l) % 2 = 0 → sibs l = zeros h ze l) :
    (k = dimHeight L.length ∧ j + 1 = L.length ∧ L.getD j ze = x)
      ∨ LastLeafAnyLengthBreak h ze L sibs k (dimHeight L.length) j x := by
  have hfold := run_root_is_fold h ze L S hrun
  rw [hroot, dimRoot, ite_eq_right hne] at hfold
  exact accepted_last_leaf_any_length_or_break h ze L sibs k (dimHeight L.length) j x
    (Nat.le_pow_clog (by norm_num) _) ⟨hj, hw.trans (Option.some.inj hfold), hz⟩

private theorem dimHeight_five : dimHeight 5 = 3 := by
  unfold dimHeight
  apply le_antisymm
  · exact (Nat.clog_le_iff_le_pow (by norm_num)).mpr (by norm_num)
  · by_contra hlt
    have hle : Nat.clog 2 5 ≤ 2 := by omega
    rw [Nat.clog_le_iff_le_pow (by norm_num)] at hle
    norm_num at hle

/-- The run over three leaves, the `root()` it reports, and the fold that is. -/
private lemma dim_three_leaf_run (h : Hash) (ze a b c : UInt256) :
    ∃ S : PushTree, Run h ze [a, b, c] S ∧ root S = some (h (h a b) (h c ze))
      ∧ rootOf h ze [a, b, c] 2 = h (h a b) (h c ze) := by
  obtain ⟨_, hrun, _, _, _, hroot⟩ := three_push_witness h ze a b c
  refine ⟨_, hrun, hroot, ?_⟩
  have hfold := run_root_is_fold h ze _ _ hrun
  rw [hroot, show ([a, b, c] : List UInt256).length = 3 from rfl, dimHeight_three, dimRoot,
    ite_eq_right (by simp)] at hfold
  exact (Option.some.inj hfold).symm

/-- The run over five leaves, the `root()` it reports, and the fold that is. -/
private lemma dim_five_leaf_run (h : Hash) (ze a b c d e : UInt256) :
    ∃ S : PushTree, Run h ze [a, b, c, d, e] S
      ∧ root S = some (h (h (h a b) (h c d)) (h (h e ze) (h ze ze)))
      ∧ rootOf h ze [a, b, c, d, e] 3 = h (h (h a b) (h c d)) (h (h e ze) (h ze ze)) := by
  obtain ⟨S, _, hrun⟩ := push_all_succeeds h ze [a, b, c, d, e]
  have hfold : rootOf h ze [a, b, c, d, e] 3 = h (h (h a b) (h c d)) (h (h e ze) (h ze ze)) := by
    simp [rootOf, levels, levelUp, zeros]
  refine ⟨S, hrun, ?_, hfold⟩
  rw [run_root_is_fold h ze _ _ hrun, show ([a, b, c, d, e] : List UInt256).length = 5 from rfl,
    dimHeight_five, dimRoot, ite_eq_right (by simp), hfold]

theorem dim_accepted_last_leaf_three_leaves (h : Hash) (ze a b c : UInt256) :
    ∃ S : PushTree,
      Run h ze [a, b, c] S ∧ root S = some (h (h a b) (h c ze)) ∧ 2 < 2 ^ 2
        ∧ walkPure h (honestSibs h ze [a, b, c] 2) 0 2 2 c = h (h a b) (h c ze)
        ∧ (∀ l < 2, (2 / 2 ^ l) % 2 = 0 → honestSibs h ze [a, b, c] 2 l = zeros h ze l)
        ∧ (2 / 2 ^ 0) % 2 = 0 ∧ dimHeight 3 = 2 := by
  obtain ⟨S, hrun, hroot, hfold⟩ := dim_three_leaf_run h ze a b c
  refine ⟨S, hrun, hroot, by norm_num, ?_, ?_, by norm_num, dimHeight_three⟩
  · rw [← hfold]
    exact honest_walk_root h ze [a, b, c] 2 2 (by norm_num)
  · have hz := zero_right_side_last h ze [a, b, c] 2 (by simp)
    rw [show ([a, b, c] : List UInt256).length - 1 = 2 from rfl] at hz
    exact hz

theorem dim_wrong_length_occurs (h : Hash) (ze a b c : UInt256) (sibs : ℕ → UInt256) :
    ∃ S : PushTree,
      Run h ze [a, b, c] S ∧ root S = some (h (h a b) (h c ze)) ∧ 0 < 2 ^ 0
        ∧ walkPure h sibs 0 0 0 (h (h a b) (h c ze)) = h (h a b) (h c ze)
        ∧ (∀ l < 0, (0 / 2 ^ l) % 2 = 0 → sibs l = zeros h ze l)
        ∧ 0 ≠ dimHeight 3
        ∧ HeightBreak h ze [a, b, c] sibs 0 (dimHeight 3) 0 (h (h a b) (h c ze)) := by
  obtain ⟨S, hrun, hroot, hfold⟩ := dim_three_leaf_run h ze a b c
  have hb := (zero_length_path_accepts_root h ze [a, b, c] sibs 2 (by norm_num)).2
  rw [hfold] at hb
  refine ⟨S, hrun, hroot, by norm_num, walkPure_zero _ _ _ _ _,
    fun l hl => absurd hl (Nat.not_lt_zero l), by rw [dimHeight_three]; norm_num, ?_⟩
  rw [dimHeight_three]
  exact hb

theorem dim_padded_entry_occurs (h : Hash) (ze a b c d e : UInt256) :
    ∃ S : PushTree,
      Run h ze [a, b, c, d, e] S
        ∧ root S = some (h (h (h a b) (h c d)) (h (h e ze) (h ze ze))) ∧ 6 < 2 ^ 3
        ∧ walkPure h (honestSibs h ze [a, b, c, d, e] 6) 0 3 6 ze
            = h (h (h a b) (h c d)) (h (h e ze) (h ze ze))
        ∧ (∀ l < 3, (6 / 2 ^ l) % 2 = 0 → honestSibs h ze [a, b, c, d, e] 6 l = zeros h ze l)
        ∧ (6 / 2 ^ 0) % 2 = 0 ∧ dimHeight 5 = 3
        ∧ 6 + 1 ≠ ([a, b, c, d, e] : List UInt256).length
        ∧ LastLeafAnyLengthBreak h ze [a, b, c, d, e] (honestSibs h ze [a, b, c, d, e] 6) 3 3 6
            ze := by
  obtain ⟨S, hrun, hroot, hfold⟩ := dim_five_leaf_run h ze a b c d e
  refine ⟨S, hrun, hroot, by norm_num, ?_, ?_, by norm_num, dimHeight_five, by simp,
    LastLeafAnyLengthBreak.paddedEntry rfl (by simp) rfl⟩
  · rw [← hfold]
    exact padded_slot_verifies h ze [a, b, c, d, e] 3 6 (by simp) (by norm_num)
  · intro l hl hev
    interval_cases l
    · simp [honestSibs, sibIdx]
    · norm_num at hev
    · norm_num at hev

theorem dim_pinned_break_occurs (h : Hash) (ze a : UInt256) :
    ∃ T : ChainTrees h ze, ∀ (created : ℕ) (ch : Contracts.Atomicity.Chain),
      T.leaves ch = [a, ze, ze] ∧ (T.backing created).height ch = 2
        ∧ root (T.state ch) = some (h (h a ze) (h ze ze))
        ∧ LastBatchAccepted (T.backing created) ch 0 (honestSibs h ze [a, ze, ze] 0) a
        ∧ (0 / 2 ^ 0) % 2 = 0 ∧ (0 / 2 ^ 1) % 2 = 0
        ∧ ZeroRightSide h ze [a, ze, ze] 2 0
        ∧ 0 + 1 ≠ (T.leaves ch).length
        ∧ PinnedBreak h ze [a, ze, ze] 0
        ∧ ¬ PathCollision h ze [a, ze, ze] (honestSibs h ze [a, ze, ze] 0) 0 2 0 a
        ∧ LastLeafAnyLengthBreak h ze [a, ze, ze] (honestSibs h ze [a, ze, ze] 0) 2 2 0 a := by
  obtain ⟨T, hT⟩ := chain_trees_exist h ze [a, ze, ze] (by simp)
  have hfold : rootOf h ze [a, ze, ze] 2 = h (h a ze) (h ze ze) := by
    simp [rootOf, levels, levelUp, zeros]
  have hzr : ZeroRightSide h ze [a, ze, ze] 2 0 := by
    intro l hl _
    interval_cases l
    · simp [honestSibs, sibIdx]
    · simp [honestSibs, sibIdx, levels, levelUp, zeros]
  have hpb : PinnedBreak h ze [a, ze, ze] 0 := PinnedBreak.entryIsEmpty (by simp) (by simp)
  have hnc : ¬ PathCollision h ze [a, ze, ze] (honestSibs h ze [a, ze, ze] 0) 0 2 0 a :=
    honest_walk_no_collision h ze [a, ze, ze] 2 0
  refine ⟨T, fun created ch => ?_⟩
  have hheight : (T.backing created).height ch = 2 := by
    show dimHeight (T.leaves ch).length = 2
    rw [hT ch]; exact dimHeight_three
  have hstored := (chain_tree_backing_is_stored h ze T created ch).2.2.2
  rw [hheight] at hstored
  have hacc : LastBatchAccepted (T.backing created) ch 0 (honestSibs h ze [a, ze, ze] 0) a := by
    refine { inRange := ?_, authenticated := ?_, zeroRightSiblings := ?_ }
    · show 0 < (T.leaves ch).length
      rw [hT ch]; simp
    · rw [hheight]
      show walkPure h (honestSibs h ze [a, ze, ze] 0) 0 2 0 a = rootOf h ze (T.leaves ch) 2
      rw [hT ch]
      exact honest_walk_root h ze [a, ze, ze] 2 0 (by norm_num)
    · rw [hheight]
      exact hzr
  refine ⟨hT ch, hheight, ?_, hacc, by norm_num, by norm_num, hzr, by rw [hT ch]; simp, hpb, hnc,
    LastLeafAnyLengthBreak.pinned rfl hpb⟩
  rw [hstored]
  show some (rootOf h ze (T.leaves ch) 2) = _
  rw [hT ch, hfold]

/-! ## The concrete instance -/

/-- `demoChainState` is the run over `[5, 7, 9]` from `setup(0)` under `demoHash`. -/
theorem demo_chain_state_run : Run demoHash 0 [5, 7, 9] demoChainState := by
  obtain ⟨hp, hrun, _⟩ := three_push_witness demoHash 0 5 7 9
  have hS : (⟨3, [9, demoHash 5 7, demoHash (demoHash 5 7) (demoHash 9 0)],
      [0, demoHash 0 0, demoHash (demoHash 0 0) (demoHash 0 0)]⟩ : PushTree) = demoChainState := by
    unfold demoChainState
    congr 1
  rw [hS] at hrun
  exact hrun

/-- The chain trees in which every chain's storage is `demoChainState`. -/
private def demoChainTrees : ChainTrees demoHash 0 where
  leaves := fun _ => [5, 7, 9]
  state := fun _ => demoChainState
  run := fun _ => demo_chain_state_run
  nonempty := fun _ => by simp

theorem dim_path_collision_occurs : Properties.DimPathCollisionOccurs := by
  have hwp : walkPair demoHash (zeros demoHash 0) 0 0 37 1 = (38, 1) := by decide
  have htp : treePair demoHash 0 [5, 7, 9] 1 0 = (20, 10) := by decide
  have hpc : PathCollision demoHash 0 [5, 7, 9] (zeros demoHash 0) 0 2 0 37 :=
    ⟨1, by norm_num, by decide, by decide⟩
  refine ⟨demoChainTrees, fun created ch => ⟨rfl, rfl, by decide, ?_, ?_, ?_,
    demo_no_pinned_break_zero, hwp, htp, hpc, LastLeafAnyLengthBreak.pathCollision rfl hpc⟩⟩
  · show dimHeight ([5, 7, 9] : List UInt256).length = 2
    exact dimHeight_three
  · refine { inRange := ?_, authenticated := ?_, zeroRightSiblings := ?_ }
    · show 0 < ([5, 7, 9] : List UInt256).length
      decide
    · show walkPure demoHash (zeros demoHash 0) 0 (dimHeight ([5, 7, 9] : List UInt256).length)
          0 37 = rootOf demoHash 0 [5, 7, 9] (dimHeight ([5, 7, 9] : List UInt256).length)
      rw [show ([5, 7, 9] : List UInt256).length = 3 from rfl, dimHeight_three]
      decide
    · exact fun _ _ _ => rfl
  · show 0 + 1 ≠ ([5, 7, 9] : List UInt256).length
    decide

/-- Every pair of the bounded set for `[5, 7, 9]` at height 2 is one of five explicit pairs. -/
private lemma demo3_pairs_mem (p : UInt256 × UInt256)
    (hp : TreePair demoHash 0 [5, 7, 9] 2 p) :
    p ∈ ([(5, 7), (9, 0), (20, 10), (0, 0), (1, 1)] : List (UInt256 × UInt256)) := by
  rcases hp with ⟨l, hl, m, hm, rfl⟩ | ⟨l, hl, rfl⟩
  · interval_cases l
    · have : m = 0 ∨ m = 1 := by simp at hm; omega
      rcases this with rfl | rfl <;> decide
    · have : m = 0 := by simp at hm; omega
      subst this; decide
  · interval_cases l <;> decide

theorem demo3_pairInjOn : PairInjOn demoHash (TreePair demoHash 0 [5, 7, 9] 2) := by
  have hW : ∀ p ∈ ([(5, 7), (9, 0), (20, 10), (0, 0), (1, 1)] : List (UInt256 × UInt256)),
      ∀ q ∈ ([(5, 7), (9, 0), (20, 10), (0, 0), (1, 1)] : List (UInt256 × UInt256)),
        demoHash p.1 p.2 = demoHash q.1 q.2 → p = q := by
    intro p hp q hq he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | exact absurd he (by decide)
  exact fun p q hp hq he => hW p (demo3_pairs_mem p hp) q (demo3_pairs_mem q hq) he

theorem demo3_entriesNotEmpty : EntriesNotEmpty 0 [5, 7, 9] := by
  intro m hm
  simp only [List.length_cons, List.length_nil] at hm
  interval_cases m <;> decide

theorem contract_path_last_iff_satisfiable : Properties.ContractPathLastIffSatisfiable := by
  have hrun := demo_chain_state_run
  have hR : Represents demoHash 0 [5, 7, 9] 2 demoChainState := by
    have := run_represents demoHash 0 _ _ hrun
    rwa [show ([5, 7, 9] : List UInt256).length = 3 from rfl, dimHeight_three] at this
  refine ⟨hrun, hR, hR.capacity, demo3_entriesNotEmpty, demo3_pairInjOn, ?_, ?_, by norm_num,
    ⟨2, 0, 0, 1, by decide, by decide⟩⟩
  · intro hz
    have h0 := hz 0 (by norm_num) (by norm_num)
    exact absurd h0 (by decide)
  · exact zero_right_side_last demoHash 0 [5, 7, 9] 2 (by simp)

end Contracts.DynamicIncrementalMerkle

/-! ## Certificates -/

namespace Contracts.DynamicIncrementalMerkle

theorem ChainTreeBackingIsStored : Properties.ChainTreeBackingIsStored :=
  chain_tree_backing_is_stored
theorem DimLastBatchAccepted : Properties.DimLastBatchAccepted := dim_last_batch_accepted
theorem ChainTreesExist : Properties.ChainTreesExist := chain_trees_exist
theorem DimLastBatchAcceptedThreeLeaves : Properties.DimLastBatchAcceptedThreeLeaves :=
  dim_last_batch_accepted_three_leaves
theorem DimLastBatchProofIdentifiesLastBatchPinned :
    Properties.DimLastBatchProofIdentifiesLastBatchPinned :=
  dim_last_batch_proof_identifies_last_batch_pinned
theorem DimAcceptedLastLeafAnyLengthOrBreak : Properties.DimAcceptedLastLeafAnyLengthOrBreak :=
  dim_accepted_last_leaf_any_length_or_break
theorem DimAcceptedLastLeafThreeLeaves : Properties.DimAcceptedLastLeafThreeLeaves :=
  dim_accepted_last_leaf_three_leaves
theorem DimWrongLengthOccurs : Properties.DimWrongLengthOccurs := dim_wrong_length_occurs
theorem DimPaddedEntryOccurs : Properties.DimPaddedEntryOccurs := dim_padded_entry_occurs
theorem DimPinnedBreakOccurs : Properties.DimPinnedBreakOccurs := dim_pinned_break_occurs
theorem DimPathCollisionOccurs : Properties.DimPathCollisionOccurs := dim_path_collision_occurs
theorem ContractPathLastHasZeroRightSide : Properties.ContractPathLastHasZeroRightSide :=
  contract_path_last_has_zero_right_side
theorem ContractPathZeroRightSideIsLastOrPinnedBreak :
    Properties.ContractPathZeroRightSideIsLastOrPinnedBreak :=
  contract_path_zero_right_side_is_last_or_pinned_break
theorem ContractPathLastIff : Properties.ContractPathLastIff := contract_path_last_iff
theorem ContractPathLastIffSatisfiable : Properties.ContractPathLastIffSatisfiable :=
  contract_path_last_iff_satisfiable

end Contracts.DynamicIncrementalMerkle
