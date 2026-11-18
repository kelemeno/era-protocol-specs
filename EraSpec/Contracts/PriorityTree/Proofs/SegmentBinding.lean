import EraSpec.Contracts.PriorityTree.Properties.SegmentBinding
import EraSpec.Contracts.Merkle.Proofs.RootPaths

/-!
# Proofs: a processed batch is the queue segment at `unprocessedIndex`, or a located break

Proofs of `../Properties/SegmentBinding.lean`. The work is in `MerkleSpec.RootPaths`
(`../../Merkle/Proofs/RootPaths.lean`): `rootPaths_frame` gives the length `PT:94` reads,
`rootPaths_any_length` the per-tree conclusion. Here: unfolding `processBatch`
(`processBatch_some`), turning a padded segment with no padding item into a queue segment
(`segment_isQueueSegment`), and gluing consecutive segments along a run
(`isQueueSegment_append`).
-/

namespace Contracts.PriorityTree.SegmentBinding

open Clear MerkleSpec MerkleSpec.Verifier MerkleSpec.RootPaths

/-! ## Unfolding `processBatch` -/

/-- A successful `processBatch` either had no items and changed nothing, or recomputed a
recorded root and advanced by the length of the array `calculateRootPaths` left. -/
theorem processBatch_some {h : Hash} {roots : UInt256 → Bool} {u : ℕ} {info : BatchInfo}
    {u' : ℕ} {mem : List UInt256} (hp : processBatch h roots u info = some (u', mem)) :
    (info.itemHashes.length = 0 ∧ u' = u ∧ mem = info.itemHashes)
    ∨ (0 < info.itemHashes.length ∧ ∃ r,
        rootPathsMem h info.leftPath info.rightPath u info.itemHashes = some (r, mem)
        ∧ roots r = true ∧ u + mem.length < wordLimit ∧ u' = u + mem.length) := by
  unfold processBatch at hp
  by_cases hn : 0 < info.itemHashes.length
  · rw [ite_eq_left hn] at hp
    right
    refine ⟨hn, ?_⟩
    split at hp
    · exact absurd hp (by simp)
    · rename_i r m' hm
      by_cases hr : roots r = true
      · rw [ite_eq_left hr] at hp
        by_cases hw : u + m'.length < wordLimit
        · rw [ite_eq_left hw] at hp
          obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hp)
          subst h2
          exact ⟨r, hm, hr, hw, h1.symm⟩
        · rw [ite_eq_right hw] at hp
          exact absurd hp (by simp)
      · rw [ite_eq_right hr] at hp
        exact absurd hp (by simp)
  · rw [ite_eq_right hn] at hp
    left
    obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hp)
    exact ⟨by omega, h1.symm, h2.symm⟩

theorem rootPaths_of_mem {h : Hash} {sp ep : List UInt256} {s : ℕ} {items : List UInt256}
    {r : UInt256} {mem : List UInt256} (hm : rootPathsMem h sp ep s items = some (r, mem)) :
    rootPaths h sp ep s items = some r := by
  unfold rootPaths; rw [hm]; rfl

theorem processBatch_advances {h : Hash} {roots : UInt256 → Bool} {u : ℕ} {info : BatchInfo}
    {u' : ℕ} {mem : List UInt256} (hp : processBatch h roots u info = some (u', mem)) :
    u' = u + info.itemHashes.length ∧ mem.length = info.itemHashes.length
    ∧ (0 < info.itemHashes.length →
        ∃ r, rootPathsMem h info.leftPath info.rightPath u info.itemHashes = some (r, mem)
          ∧ roots r = true) := by
  rcases processBatch_some hp with ⟨h0, hu, hmem⟩ | ⟨_, r, hm, hr, _, hu⟩
  · exact ⟨by omega, by rw [hmem], fun hn => absurd h0 (by omega)⟩
  · have hlen := (rootPaths_frame hm).1
    exact ⟨by rw [hu, hlen], hlen, fun _ => ⟨r, hm, hr⟩⟩

/-! ## Queue segments -/

theorem getD_take_lt (Q : List UInt256) (m k : ℕ) (d : UInt256) (hk : k < m) :
    (Q.take m).getD k d = Q.getD k d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hk]

theorem getD_take_ge (Q : List UInt256) (m k : ℕ) (d : UInt256) (hk : m ≤ k) :
    (Q.take m).getD k d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_right (by omega : ¬ k < m)]
  rfl

/-- **A padded prefix segment with no padding item is a queue segment.** If the items are the
entries `[u, u + n)` of the tree over `Q.take m` (padding `z`), `m ≤ Q.length`, and no item is
`z`, then every index is below `m`, and the items are `Q[u], …, Q[u + n - 1]`. -/
theorem segment_isQueueSegment (z : UInt256) (Q : List UInt256) (m u : ℕ)
    (items : List UInt256) (hm : m ≤ Q.length) (hn : 0 < items.length) (hz : z ∉ items)
    (hseg : items = RootPaths.treeSegment z (Q.take m) u items.length) : IsQueueSegment Q u items := by
  have hitem : ∀ i, i < items.length → items.getD i 0 = (Q.take m).getD (u + i) z := by
    intro i hi
    conv_lhs => rw [hseg]
    unfold RootPaths.treeSegment
    rw [getD_map_range _ _ _ hi]
  have hlt : ∀ i, i < items.length → u + i < m := by
    intro i hi
    by_contra hge
    apply hz
    have hz' : items.getD i 0 = z := by
      rw [hitem i hi, getD_take_ge _ _ _ _ (by omega)]
    rw [← hz']
    exact Verifier.getD_mem items i 0 hi
  have hend := hlt (items.length - 1) (by omega)
  refine ⟨by omega, ?_⟩
  refine MerkleSpec.Pinned.ext_getD' 0 _ _ ?_ ?_
  · rw [List.length_take, List.length_drop]; omega
  · intro i hi
    rw [List.length_take, List.length_drop] at hi
    have hi' : i < items.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hi', List.getElem?_drop,
      ← List.getD_eq_getElem?_getD, hitem i hi', getD_take_lt _ _ _ _ (hlt i hi')]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega : u + i < Q.length)]
    rfl

theorem isQueueSegment_nil (Q : List UInt256) (u : ℕ) (hu : u ≤ Q.length) :
    IsQueueSegment Q u [] :=
  ⟨by simpa using hu, by simp⟩

/-- **Consecutive segments glue.** -/
theorem isQueueSegment_append (Q : List UInt256) (u : ℕ) (A B : List UInt256)
    (hA : IsQueueSegment Q u A) (hB : IsQueueSegment Q (u + A.length) B) :
    IsQueueSegment Q u (A ++ B) := by
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  refine ⟨by rw [List.length_append]; omega, ?_⟩
  rw [List.length_append, List.take_add, hA2, List.drop_drop, hB2]

/-! ## One batch -/

theorem processBatch_segment_or_break (h : Hash) (z : UInt256) (roots : UInt256 → Bool)
    (Q : List UInt256) (log : List (ℕ × ℕ)) (u : ℕ) (info : BatchInfo) (u' : ℕ)
    (mem : List UInt256) (hroots : RootsAreLoggedPrefixRoots h z roots Q log)
    (hp : processBatch h roots u info = some (u', mem)) (hn : 0 < info.itemHashes.length) :
    u' = u + info.itemHashes.length
    ∧ (rootPaths h info.leftPath info.rightPath u info.itemHashes = some 0
      ∨ ∃ p ∈ log,
          rootPaths h info.leftPath info.rightPath u info.itemHashes
            = some (rootOf h z (Q.take p.1) p.2)
          ∧ ((info.leftPath.length = p.2
                ∧ info.itemHashes = RootPaths.treeSegment z (Q.take p.1) u info.itemHashes.length)
            ∨ TreeBreak h z (Q.take p.1) p.2 u info)) := by
  obtain ⟨hu', _, hroot⟩ := processBatch_advances hp
  refine ⟨hu', ?_⟩
  obtain ⟨r, hm, hr⟩ := hroot hn
  have hrp := rootPaths_of_mem hm
  rcases hroots.2 r hr with h0 | ⟨p, hpl, hreq⟩
  · left; rw [hrp, h0]
  · right
    refine ⟨p, hpl, by rw [hrp, hreq], ?_⟩
    rw [hreq] at hrp
    rcases rootPaths_any_length h z (Q.take p.1) p.2 _ _ u _ hrp with
      ⟨hP, hseg⟩ | ⟨hP, hc⟩ | ⟨hP, hb⟩
    · exact Or.inl ⟨hP, hseg⟩
    · rw [hP] at hc
      exact Or.inr (Or.inl ⟨hP, hc⟩)
    · exact Or.inr (Or.inr ⟨hP, hb⟩)

theorem processBatch_queue_segment_or_break (h : Hash) (z : UInt256) (roots : UInt256 → Bool)
    (Q : List UInt256) (log : List (ℕ × ℕ)) (u : ℕ) (info : BatchInfo) (u' : ℕ)
    (mem : List UInt256) (hroots : RootsAreLoggedPrefixRoots h z roots Q log)
    (hp : processBatch h roots u info = some (u', mem)) (hn : 0 < info.itemHashes.length)
    (hz : z ∉ info.itemHashes) :
    u' = u + info.itemHashes.length
    ∧ (IsQueueSegment Q u info.itemHashes ∨ BatchBreak h z Q log u info) := by
  obtain ⟨hu', hcase⟩ := processBatch_segment_or_break h z roots Q log u info u' mem hroots hp hn
  refine ⟨hu', ?_⟩
  rcases hcase with h0 | ⟨p, hpl, hreq, ⟨_, hseg⟩ | htb⟩
  · exact Or.inr (Or.inl h0)
  · exact Or.inl (segment_isQueueSegment z Q p.1 u _ (hroots.1 p hpl) hn hz hseg)
  · exact Or.inr (Or.inr ⟨p, hpl, hreq, htb⟩)

/-! ## Runs -/

theorem processRun_advance (h : Hash) (roots : UInt256 → Bool) :
    ∀ {u₀ : ℕ} {steps : List (ℕ × BatchInfo)} {u₁ : ℕ}, ProcessRun h roots u₀ steps u₁ →
      u₁ = u₀ + (runItems steps).length := by
  intro u₀ steps u₁ hrun
  induction hrun with
  | nil u => simp [runItems]
  | @cons u u' u'' info mem rest hp _ ih =>
    have hadv := (processBatch_advances hp).1
    have hitems : runItems ((u, info) :: rest) = info.itemHashes ++ runItems rest := by
      unfold runItems; rw [List.flatMap_cons]
    rw [hitems, List.length_append, ih, hadv]
    omega

theorem processed_run (h : Hash) (z : UInt256) (roots : UInt256 → Bool) (Q : List UInt256)
    (log : List (ℕ × ℕ)) (hroots : RootsAreLoggedPrefixRoots h z roots Q log) :
    ∀ {u₀ : ℕ} {steps : List (ℕ × BatchInfo)} {u₁ : ℕ}, ProcessRun h roots u₀ steps u₁ →
      u₀ ≤ Q.length → (∀ p ∈ steps, z ∉ p.2.itemHashes) →
      IsQueueSegment Q u₀ (runItems steps) ∨ ∃ p ∈ steps, BatchBreak h z Q log p.1 p.2 := by
  intro u₀ steps u₁ hrun
  induction hrun with
  | nil u =>
    intro hu _
    exact Or.inl (isQueueSegment_nil Q u hu)
  | @cons u u' u'' info mem rest hp _ ih =>
    intro hu hz
    have hzi : z ∉ info.itemHashes := hz (u, info) (by simp)
    have hzr : ∀ p ∈ rest, z ∉ p.2.itemHashes := fun p hpm => hz p (by simp [hpm])
    have hitems : runItems ((u, info) :: rest) = info.itemHashes ++ runItems rest := by
      unfold runItems; rw [List.flatMap_cons]
    rw [hitems]
    by_cases hn : 0 < info.itemHashes.length
    · obtain ⟨hu', hcase⟩ :=
        processBatch_queue_segment_or_break h z roots Q log u info u' mem hroots hp hn hzi
      rcases hcase with hseg | hb
      · have hu'Q : u' ≤ Q.length := by rw [hu']; exact hseg.1
        rcases ih hu'Q hzr with hrestseg | ⟨p, hpm, hpb⟩
        · left
          rw [hu'] at hrestseg
          exact isQueueSegment_append Q u _ _ hseg hrestseg
        · exact Or.inr ⟨p, by simp [hpm], hpb⟩
      · exact Or.inr ⟨(u, info), by simp, hb⟩
    · have h0 : info.itemHashes = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hu' : u' = u := by
        have := (processBatch_advances hp).1
        rw [h0] at this; simpa using this
      rw [h0, List.nil_append]
      rcases ih (by rw [hu']; exact hu) hzr with hrestseg | ⟨p, hpm, hpb⟩
      · left; rw [hu'] at hrestseg; exact hrestseg
      · exact Or.inr ⟨p, by simp [hpm], hpb⟩

theorem processBatch_monotone (h : Hash) (roots roots' : UInt256 → Bool) (u : ℕ)
    (info : BatchInfo) (x : ℕ × List UInt256) (hsub : ∀ r, roots r = true → roots' r = true)
    (hp : processBatch h roots u info = some x) : processBatch h roots' u info = some x := by
  obtain ⟨u', mem⟩ := x
  rcases processBatch_some hp with ⟨h0, hu, hmem⟩ | ⟨hn, r, hm, hr, hw, hu⟩
  · unfold processBatch
    rw [ite_eq_right (by omega), hu, hmem]
  · unfold processBatch
    rw [ite_eq_left hn, hm]
    simp only
    rw [ite_eq_left (hsub r hr), ite_eq_left hw, hu]

/-! ## The breaks -/

theorem setup_root_hit_cases (h : Hash) (sp ep : List UInt256) (u : ℕ) (items : List UInt256)
    (hr : rootPaths h sp ep u items = some 0) :
    (sp = [] ∧ u = 0 ∧ items = [0])
    ∨ (sp ≠ [] ∧
        h (walkPair h (rangeSib h sp ep u items (u + 0)) 0 (u + 0) (items.getD 0 0)
            (sp.length - 1)).1
          (walkPair h (rangeSib h sp ep u items (u + 0)) 0 (u + 0) (items.getD 0 0)
            (sp.length - 1)).2 = 0) := by
  by_cases hsp : sp = []
  · left
    obtain ⟨_, hu, hn, hr0⟩ := RootPathsEmptyPathIsTheItem.1 h sp ep u items 0 hr hsp
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hn
    subst ha
    exact ⟨hsp, hu, by rw [hr0]; rfl⟩
  · right
    refine ⟨hsp, ?_⟩
    obtain ⟨hg, _⟩ := guard_of_rootPaths hr
    obtain ⟨_, _, hn, _⟩ := (guard_eq_none_iff sp ep u items).mp hg
    obtain ⟨_, hw⟩ := item_walk hr 0 hn
    obtain ⟨k, hk⟩ : ∃ k, sp.length = k + 1 :=
      ⟨sp.length - 1, by have := List.length_pos_iff.mpr hsp; omega⟩
    rw [hk, walkPure_succ_eq_walkPair] at hw
    rw [hk, Nat.add_sub_cancel]
    exact hw

theorem honest_batch_no_tree_break (h : Hash) (z : UInt256) (L : List UInt256) (H u n : ℕ)
    (hn : 1 ≤ n) (hun : u + n ≤ 2 ^ H) (hH : H < 256) :
    ¬ TreeBreak h z L H u
      ⟨honestPath h z L u H, honestPath h z L (u + n - 1) H, RootPaths.treeSegment z L u n⟩ := by
  rintro (⟨_, i, hi, hc⟩ | ⟨hne, _⟩)
  · have hi' : i < n := by simpa [treeSegment_length] using hi
    exact (rootPaths_honest_no_break h z L H u n hn hun hH i hi').1 hc
  · exact hne (honestPath_length h z L u H)

/-! ## The concrete queue -/

theorem witness_premise :
    RootsAreLoggedPrefixRoots rangeToyHash 7 witnessRoots witnessQueue witnessLog := by
  refine ⟨by decide, fun r hr => ?_⟩
  simp only [witnessRoots, Bool.or_eq_true, beq_iff_eq] at hr
  rcases hr with ((h0 | h1) | h2) | h3
  · exact Or.inl h0
  · exact Or.inr ⟨(1, 0), by decide, h1⟩
  · exact Or.inr ⟨(2, 1), by decide, h2⟩
  · exact Or.inr ⟨(3, 2), by decide, h3⟩

/-- Against a logged tree whose root the batch does not return, there is no break. -/
theorem no_break_of_root_ne (h : Hash) (z : UInt256) (Q : List UInt256) (log : List (ℕ × ℕ))
    (u : ℕ) (info : BatchInfo) (r : UInt256)
    (hr : rootPaths h info.leftPath info.rightPath u info.itemHashes = some r) (hr0 : r ≠ 0)
    (hlog : ∀ p ∈ log, rootOf h z (Q.take p.1) p.2 = r → ¬ TreeBreak h z (Q.take p.1) p.2 u info) :
    ¬ BatchBreak h z Q log u info := by
  rintro (h0 | ⟨p, hpl, hreq, htb⟩)
  · rw [hr] at h0; exact hr0 (Option.some.inj h0)
  · rw [hr] at hreq
    exact hlog p hpl (Option.some.inj hreq).symm htb

/-! ## Certificates -/

theorem ProcessBatchAdvancesByLength : Properties.ProcessBatchAdvancesByLength :=
  fun _ _ _ _ _ _ hp => processBatch_advances hp

theorem ExecutePriorityHashesSubmittedItems : Properties.ExecutePriorityHashesSubmittedItems := by
  intro h kpair e0 roots u nL1 poh info u' mem hx
  unfold executePriority at hx
  by_cases h1 : info.itemHashes.length ≠ nL1
  · rw [ite_eq_left h1] at hx; exact absurd hx (by simp)
  · rw [ite_eq_right h1] at hx
    by_cases h2 : rollingHash kpair e0 info.itemHashes ≠ poh
    · rw [ite_eq_left h2] at hx; exact absurd hx (by simp)
    · rw [ite_eq_right h2] at hx
      exact ⟨not_not.mp h1, not_not.mp h2, hx⟩

theorem HashAfterCallRejectsHonestBatch : Properties.HashAfterCallRejectsHonestBatch := by
  unfold Properties.HashAfterCallRejectsHonestBatch
  decide

theorem ProcessBatchSegmentOrBreak : Properties.ProcessBatchSegmentOrBreak :=
  processBatch_segment_or_break

theorem ProcessBatchQueueSegmentOrBreak : Properties.ProcessBatchQueueSegmentOrBreak :=
  processBatch_queue_segment_or_break

theorem ProcessedRunIsQueueSegmentOrBreak : Properties.ProcessedRunIsQueueSegmentOrBreak :=
  fun h z roots Q log _ _ _ hroots hrun hu hz =>
    ⟨processRun_advance h roots hrun, processed_run h z roots Q log hroots hrun hu hz⟩

theorem ProcessBatchMonotoneInRoots : Properties.ProcessBatchMonotoneInRoots :=
  processBatch_monotone

theorem SetupRootHitCases : Properties.SetupRootHitCases := setup_root_hit_cases

theorem HonestBatchNoTreeBreak : Properties.HonestBatchNoTreeBreak := honest_batch_no_tree_break

theorem SegmentBindingWitness : Properties.SegmentBindingWitness := by
  have hb2 : (⟨honestPath rangeToyHash 7 witnessQueue 1 2,
      honestPath rangeToyHash 7 witnessQueue 2 2, [12, 13]⟩ : BatchInfo)
      = ⟨honestPath rangeToyHash 7 (witnessQueue.take 3) 1 2,
          honestPath rangeToyHash 7 (witnessQueue.take 3) (1 + 2 - 1) 2,
          RootPaths.treeSegment 7 (witnessQueue.take 3) 1 2⟩ := by
    rfl
  refine ⟨witness_premise, by decide, by decide,
    ProcessRun.cons (mem := [11]) (by decide)
      (ProcessRun.cons (mem := [186, 47]) (by decide) (ProcessRun.nil 3)),
    Nat.zero_le _, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · refine no_break_of_root_ne _ _ _ _ _ _ 11 (by decide) (by decide) ?_
    intro p hpl hroot
    simp only [witnessLog, List.mem_cons, List.not_mem_nil, or_false] at hpl
    rcases hpl with rfl | rfl | rfl
    · rintro (⟨_, i, hi, hc⟩ | ⟨hne, _⟩)
      · obtain ⟨j, hj, _⟩ := hc; omega
      · exact hne rfl
    · exact absurd hroot (by decide)
    · exact absurd hroot (by decide)
  · refine no_break_of_root_ne _ _ _ _ _ _ 186 (by decide) (by decide) ?_
    intro p hpl hroot
    simp only [witnessLog, List.mem_cons, List.not_mem_nil, or_false] at hpl
    rcases hpl with rfl | rfl | rfl
    · exact absurd hroot (by decide)
    · exact absurd hroot (by decide)
    · rw [hb2]
      exact honest_batch_no_tree_break rangeToyHash 7 (witnessQueue.take 3) 2 1 2 (by norm_num)
        (by norm_num) (by norm_num)

theorem PaddingItemsAdvancePastQueue : Properties.PaddingItemsAdvancePastQueue := by
  have hb : (⟨honestPath rangeToyHash 7 witnessQueue 3 2,
      honestPath rangeToyHash 7 witnessQueue 3 2, [7]⟩ : BatchInfo)
      = ⟨honestPath rangeToyHash 7 (witnessQueue.take 3) 3 2,
          honestPath rangeToyHash 7 (witnessQueue.take 3) (3 + 1 - 1) 2,
          RootPaths.treeSegment 7 (witnessQueue.take 3) 3 1⟩ := by
    rfl
  refine ⟨witness_premise, by decide, by decide, by decide, ?_⟩
  refine no_break_of_root_ne _ _ _ _ _ _ 186 (by decide) (by decide) ?_
  intro p hpl hroot
  simp only [witnessLog, List.mem_cons, List.not_mem_nil, or_false] at hpl
  rcases hpl with rfl | rfl | rfl
  · exact absurd hroot (by decide)
  · exact absurd hroot (by decide)
  · rw [hb]
    exact honest_batch_no_tree_break rangeToyHash 7 (witnessQueue.take 3) 2 3 1 (by norm_num)
      (by norm_num) (by norm_num)

theorem SetupRootAcceptsZeroItem : Properties.SetupRootAcceptsZeroItem :=
  ⟨witness_premise, by decide, by decide, Or.inl (by decide)⟩

end Contracts.PriorityTree.SegmentBinding
