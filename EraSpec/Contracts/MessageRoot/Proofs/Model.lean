import EraSpec.Contracts.MessageRoot.Properties.Model
import EraSpec.Contracts.MessageRoot.Proofs.Steps
import EraSpec.Contracts.Merkle.Proofs.RootForgeryPinned

/-!
# Proofs: what the message root guarantees on every run

Each `Properties.X` of `Properties/Model.lean` is proved as `X`.  The engine is
`inv_reachable` (`Proofs/Invariant.lean`: `initialize` establishes `Inv`, every call keeps it)
and `step_facts` (`Proofs/Steps.lean`).
-/

namespace Contracts.MessageRoot

open AttackVectors.CapacityInvariant (TreeDims)

theorem ReachableInv : Properties.ReachableInv :=
  fun _ _ _ h => inv_reachable h

theorem InvKeptByEveryCall : Properties.InvKeptByEveryCall :=
  fun _ _ _ _ _ _ hI h => inv_exec hI h

theorem ChainTreeSetUpOnce : Properties.ChainTreeSetUpOnce :=
  fun _ _ _ hs => (inv_reachable hs).setups

theorem ChainIndexBijection : Properties.ChainIndexBijection := by
  intro H cfg s hs
  have hI := inv_reachable hs
  refine ⟨hI.self_at_zero, hI.self_index, hI.count_pos, ?_, ?_, fun c hc => hI.reg_slot hc⟩
  · intro i j hi hj hij
    rw [← hI.index_of_slot i hi, ← hI.index_of_slot j hj, hij]
  · intro c
    constructor
    · intro hc
      obtain ⟨h1, h2⟩ := hI.reg_slot hc
      exact ⟨_, h1, h2⟩
    · rintro ⟨i, hi, rfl⟩
      exact hI.slot_reg hi

theorem ChainAddedOnce : Properties.ChainAddedOnce := by
  intro H cfg s env c start hs
  have hI := inv_reachable hs
  refine ⟨fun hc => ?_, fun t h => ?_⟩
  · simp only [exec, hc]
    split_ifs <;> rfl
  · simp only [exec] at h
    split_ifs at h with h1 h2
    have hc : chainRegistered cfg s c = false := by simpa using h2
    have hsend : env.sender = cfg.bridgehub ∨ env.sender = cfg.chainAssetHandler := by
      by_cases hb : env.sender = cfg.bridgehub
      · exact Or.inl hb
      · exact Or.inr (by push Not at h1; exact h1 hb)
    obtain ⟨S', R, k, _, _, _, _, rfl⟩ := addNewChainInternal_some h
    have hk0 : s.chainCount ≠ 0 := by have := hI.count_pos; omega
    exact ⟨hsend, hc, by simp [chainRegistered, hk0], by simp, rfl, by simp, by simp,
      sharedLeaves_addNewChain hI hc rfl rfl rfl⟩

theorem RegistrationStable : Properties.RegistrationStable := by
  intro H cfg s t tr hs hrun
  induction hrun with
  | nil => exact ⟨le_rfl, fun _ _ => rfl, fun _ hc => ⟨hc, rfl⟩⟩
  | @snoc t' u' tr' e call hr hx ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hI := inv_reachable (reachable_run hs hr)
    refine ⟨h1.trans (step_facts hI hx 0).count_le, fun i hi => ?_, fun c hc => ?_⟩
    · rw [(step_facts hI hx 0).slots_keep i (by omega), h2 i hi]
    · obtain ⟨hc', hidx⟩ := h3 c hc
      obtain ⟨hc'', hidx', _⟩ := (step_facts hI hx c).reg_keep hc'
      exact ⟨hc'', hidx'.trans hidx⟩

theorem AggregatedRootFormula : Properties.AggregatedRootFormula := by
  intro H cfg s hs
  have hI := inv_reachable hs
  have hcount : s.chainCount ≠ 0 := by have := hI.count_pos; omega
  obtain ⟨_, hH⟩ := Contracts.FullMerkle.reachable_represents _ _ _ hI.tree_reach
  have hnum : s.sharedTree.leafNumber = s.chainCount := by
    rw [hI.tree_rep.leafNumber_eq, sharedLeaves_length]
  unfold getAggregatedRoot
  rw [if_neg hcount, Contracts.FullMerkle.root_is_fold _ _ _ _ hI.tree_rep, hH, hnum]

theorem sharedLeaves_eq_of {H : Hashes} {cfg : Config} {s s' : State} (hI : Inv H cfg s)
    (hcount : s.chainCount = s'.chainCount)
    (hslot : ∀ i, i < s.chainCount → s.chainIndexToId i = s'.chainIndexToId i)
    (hleaves : ∀ c, chainRegistered cfg s c = true → s.chainLeaves c = s'.chainLeaves c) :
    sharedLeaves H s = sharedLeaves H s' := by
  unfold sharedLeaves
  rw [← hcount]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [← hslot i hi, hleaves _ (hI.slot_reg hi)]

theorem AggregatedRootDeterminedByChainTrees :
    Properties.AggregatedRootDeterminedByChainTrees := by
  intro H cfg s s' hs hs' hcount hslot hleaves
  rw [AggregatedRootFormula H cfg s hs, AggregatedRootFormula H cfg s' hs',
    sharedLeaves_eq_of (inv_reachable hs) hcount hslot hleaves, hcount]

theorem AggregatedRootPinsChainRootOrCollision :
    Properties.AggregatedRootPinsChainRootOrCollision := by
  intro H cfg s s' c hs hs' hcount hc hslot heq
  have hI := inv_reachable hs
  rw [AggregatedRootFormula H cfg s hs, AggregatedRootFormula H cfg s' hs', ← hcount] at heq
  have heq' := Option.some.inj heq
  obtain ⟨hidx, hto⟩ := hI.reg_slot hc
  have hcap : s.chainIndex c <
      2 ^ (AttackVectors.CapacityInvariant.push^[s.chainCount] (⟨0, 0⟩ : TreeDims)).height := by
    obtain ⟨_, hH⟩ := Contracts.FullMerkle.reachable_represents _ _ _ hI.tree_reach
    have hc2 := hI.tree_rep.capacity
    rw [sharedLeaves_length] at hc2
    rw [hI.tree_rep.leafNumber_eq, sharedLeaves_length] at hH
    rw [← hH]; omega
  rcases MerkleSpec.Pinned.root_pins_entry_or_collision _ _ _ _ _ _ hcap heq' with h | h
  · have e1 : (sharedLeaves H s).getD (s.chainIndex c) cfg.emptyHash
        = H.chainIdLeaf (chainRootOf H (s.chainLeaves c)) c := by
      simp [List.getD_eq_getElem?_getD, sharedLeaves, hidx, hto]
    have e2 : (sharedLeaves H s').getD (s.chainIndex c) cfg.emptyHash
        = H.chainIdLeaf (chainRootOf H (s'.chainLeaves c)) c := by
      have hlt : s.chainIndex c < s'.chainCount := by omega
      simp [List.getD_eq_getElem?_getD, sharedLeaves, hlt, hslot]
    rw [e1, e2] at h
    by_cases hr : chainRootOf H (s.chainLeaves c) = chainRootOf H (s'.chainLeaves c)
    · exact Or.inl hr
    · exact Or.inr (Or.inl ⟨hr, h⟩)
  · exact Or.inr (Or.inr h)

theorem HistoricalRootIsAggregated : Properties.HistoricalRootIsAggregated := by
  intro H cfg s hs
  have hI := inv_reachable hs
  have hcount : s.chainCount ≠ 0 := by have := hI.count_pos; omega
  unfold getAggregatedRoot
  rw [if_neg hcount, hI.hist]

theorem BatchRootsBeyondCurrentAreZero : Properties.BatchRootsBeyondCurrentAreZero := by
  intro H cfg s hs
  have hI := inv_reachable hs
  exact ⟨hI.beyond_zero, hI.unreg_empty⟩

theorem ChainTreeIsOrderedLog : Properties.ChainTreeIsOrderedLog := by
  intro H cfg s hs c
  exact (inv_reachable hs).log c

theorem BatchRootsWriteOnce : Properties.BatchRootsWriteOnce := by
  intro H cfg s t tr c n hs hrun hn
  induction hrun with
  | nil => exact ⟨rfl, rfl⟩
  | @snoc t' u' tr' e call hr hx ih =>
    obtain ⟨h1, h2⟩ := ih
    have hI := inv_reachable (reachable_run hs hr)
    obtain ⟨h3, h4⟩ := (step_facts hI hx c).roots_once n (by rw [h1]; exact hn)
    exact ⟨h3.trans h1, h4.trans h2⟩

theorem ChainTreeAppendOnly : Properties.ChainTreeAppendOnly := by
  intro H cfg s t tr c hs hrun
  induction hrun with
  | nil => exact List.prefix_refl _
  | @snoc t' u' tr' e call hr hx ih =>
    have hI := inv_reachable (reachable_run hs hr)
    exact ih.trans (step_facts hI hx c).leaves_prefix

theorem CurrentBatchMonotone : Properties.CurrentBatchMonotone := by
  intro H cfg s t tr c hs hrun hc
  suffices chainRegistered cfg t c = true ∧
      s.currentChainBatchNumber c ≤ t.currentChainBatchNumber c from this.2
  induction hrun with
  | nil => exact ⟨hc, le_rfl⟩
  | @snoc t' u' tr' e call hr hx ih =>
    obtain ⟨h1, h2⟩ := ih
    have hI := inv_reachable (reachable_run hs hr)
    obtain ⟨h3, _, h4⟩ := (step_facts hI hx c).reg_keep h1
    exact ⟨h3, h2.trans h4⟩

theorem AppendExact : Properties.AppendExact := by
  intro H cfg s env c n r hs
  have hI := inv_reachable hs
  refine ⟨fun t h => ?_, fun t h => ?_⟩
  · simp only [exec] at h
    split_ifs at h with h1
    push Not at h1
    obtain ⟨s₁, h₁, h₂⟩ : ∃ s₁, recordChainBatchRoot cfg c n r s = some s₁
        ∧ pushChainBatchRoot H env c n r s₁ = some t := by
      cases hrec : recordChainBatchRoot cfg c n r s with
      | none => rw [hrec] at h; cases h
      | some s₁ => rw [hrec] at h; exact ⟨s₁, rfl, h⟩
    obtain ⟨hc, hr, _, _, hn, rfl⟩ := recordChainBatchRoot_some h₁
    obtain ⟨S', R, k, _, _, _, rfl⟩ := pushChainBatchRoot_some h₂
    refine ⟨h1, hc, hr, hn, by simp [upd2_apply], by simp, by simp [upd2_apply], by simp,
      fun c' hc' => ⟨by simp [Function.update_of_ne hc'], ?_, by simp [Function.update_of_ne hc']⟩⟩
    funext m; simp [upd2_apply, hc']
  · simp only [exec] at h
    split_ifs at h with h1
    push Not at h1
    obtain ⟨hc, hr, _, _, hn, rfl⟩ := recordChainBatchRoot_some h
    exact ⟨h1, hc, hr, hn, by simp [upd2_apply], by simp, rfl, rfl, rfl⟩

theorem emitRoot_bind_isSome {env : Env} {s : State} (f : State → State)
    (h : s.interopRootLogId + 1 < UInt256.size) :
    ((emitRoot env s).bind fun x => some (f x)).isSome = true := by
  unfold emitRoot
  split_ifs <;> rfl

theorem AppendLiveness : Properties.AppendLiveness := by
  intro H cfg s env c n r hs hsend hc hr hn hof hlog
  have hI := inv_reachable hs
  have h0 : s.chainBatchRoots c n = 0 := hI.beyond_zero c n (by omega)
  have hrec : recordChainBatchRoot cfg c n r s = some { s with
      chainBatchRoots := upd2 s.chainBatchRoots c n r
      currentChainBatchNumber :=
        Function.update s.currentChainBatchNumber c (s.currentChainBatchNumber c + 1) } := by
    unfold recordChainBatchRoot
    have hof' : ¬ UInt256.size ≤ s.currentChainBatchNumber c + 1 := by omega
    rw [if_neg (by simp [hc]), if_neg hr, if_neg (by simp [h0]), if_neg hof', if_neg (by omega)]
  obtain ⟨hidx, _⟩ := hI.reg_slot hc
  obtain ⟨S'', hp, -, -, -⟩ := Contracts.FullMerkle.updateLeaf_computes_root _ _ _ _
    (s.chainIndex c)
    (H.chainIdLeaf (chainRootOf H (s.chainLeaves c ++ [H.batchLeaf r n env.timestamp])) c)
    hI.tree_rep (by rw [sharedLeaves_length]; exact hidx)
  apply Option.isSome_iff_exists.1
  simp only [exec, hsend, ne_eq, not_true_eq_false, if_false, hrec, Option.bind_some]
  have hset : s.chainTreeSetups c ≠ 0 := by simp [hI.setups c, hc]
  unfold pushChainBatchRoot
  simp only [hset, if_false, Option.bind_eq_bind, Option.pure_def, hp, Option.bind_some]
  exact emitRoot_bind_isSome _ hlog

theorem AddNewChainLiveness : Properties.AddNewChainLiveness := by
  intro H cfg s env c start hs hsend hc hcount hlog
  have hI := inv_reachable hs
  obtain ⟨S', hp, -, -⟩ := Contracts.FullMerkle.pushNewLeaf_computes_root _ _ _ _
    (H.chainIdLeaf 0 c) hI.tree_rep
  have hguard : ¬ (env.sender ≠ cfg.bridgehub ∧ env.sender ≠ cfg.chainAssetHandler) := by tauto
  apply Option.isSome_iff_exists.1
  simp only [exec, hguard, if_false, hc, Bool.false_eq_true]
  unfold addNewChainInternal
  simp only [hcount, if_true, Option.bind_eq_bind, Option.pure_def, hp, Option.bind_some]
  exact emitRoot_bind_isSome _ hlog

theorem GenesisSeedIsFirstLeaf : Properties.GenesisSeedIsFirstLeaf := by
  intro H cfg s env c hs t h
  have hI := inv_reachable hs
  simp only [exec] at h
  split_ifs at h with h1 h2 h3 h4 h5
  push Not at h1 h4 h5
  have hnil := hI.leaves_nil_of_fresh h4 h5
  obtain ⟨S', R, k, _, _, _, rfl⟩ := pushChainBatchRoot_some h
  exact ⟨h1, hnil, h4, h4, by simp [upd2_apply], by simp [hnil]⟩

theorem ChainWritersOnly : Properties.ChainWritersOnly := by
  intro H cfg s t tr c hs hrun hw
  induction hrun with
  | nil => exact ⟨rfl, rfl, rfl, fun _ => rfl⟩
  | @snoc t' u' tr' e call hr hx ih =>
    have hI := inv_reachable (reachable_run hs hr)
    obtain ⟨h1, h2, h3, h4⟩ := ih (fun p hp => hw p (List.mem_append_left _ hp))
    obtain ⟨hz, hb⟩ := hw (e, call) (List.mem_append_right _ (List.mem_singleton_self _))
    obtain ⟨g1, g2, g3, g4⟩ := (step_facts hI hx c).writers hz hb
    refine ⟨g1.trans h1, g2.trans h2, g3.trans h3, fun hcah => ?_⟩
    rw [g4 (hcah (e, call) (List.mem_append_right _ (List.mem_singleton_self _))),
      h4 (fun p hp => hcah p (List.mem_append_left _ hp))]

theorem ProofRootIsRecordedRoot : Properties.ProofRootIsRecordedRoot := by
  intro H cfg s env c n proven hs
  have hI := inv_reachable hs
  refine ⟨by simp [finalNodeAccepts, getChainBatchRoot], fun hv h => ?_⟩
  unfold finalNodeAccepts getChainBatchRoot at h
  by_cases hn0 : n = 0
  · simp [hn0] at h
  · by_cases hr : s.chainBatchRoots c n = 0
    · rw [if_neg hn0, if_neg (by simpa using hr), if_neg (by omega)] at h
      simp at h
    · rw [if_neg hn0, if_pos hr] at h
      simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq] at h
      refine ⟨Nat.pos_of_ne_zero hn0, ?_, h.1, h.1 ▸ h.2⟩
      by_contra hlt
      exact hr (hI.beyond_zero c n (by omega))

theorem FinalNodeAcceptsIff : Properties.FinalNodeAcceptsIff := by
  intro cfg env s c n proven
  unfold finalNodeAccepts getChainBatchRoot
  by_cases hn0 : n = 0
  · subst hn0; simp
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn0
    rw [if_neg hn0]
    by_cases hr : s.chainBatchRoots c n = 0
    · rw [if_neg (not_not.2 hr)]
      by_cases hv : n < cfg.v31Upgrade c
      · rw [if_pos hv]
        simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨hpos, h1 ▸ h2, Or.inr ⟨hr, hv, h1⟩⟩
        · rintro ⟨-, h1, h2 | ⟨-, -, h2⟩⟩
          · exact absurd (h2.symm.trans hr) h1
          · exact ⟨h2, h2 ▸ h1⟩
      · rw [if_neg hv]
        simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨-, h2⟩; exact absurd rfl h2
        · rintro ⟨-, h1, h2 | ⟨-, h2, -⟩⟩
          · exact absurd (h2.symm.trans hr) h1
          · exact absurd h2 hv
    · rw [if_pos hr]
      simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨hpos, h1 ▸ h2, Or.inl h1⟩
      · rintro ⟨-, -, h2 | ⟨h2, -⟩⟩
        · exact ⟨h2, hr⟩
        · exact absurd h2 hr

theorem SettledBatchRootsFrozen : Properties.SettledBatchRootsFrozen := by
  intro H cfg s t tr c n hs hrun hc hn h0
  have key : chainRegistered cfg t c = true
      ∧ s.currentChainBatchNumber c ≤ t.currentChainBatchNumber c
      ∧ ∀ m, m ≤ s.currentChainBatchNumber c → t.chainBatchRoots c m = s.chainBatchRoots c m := by
    induction hrun with
    | nil => exact ⟨hc, le_rfl, fun _ _ => rfl⟩
    | @snoc t' u' tr' e call hr hx ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      have hI := inv_reachable (reachable_run hs hr)
      obtain ⟨g1, _, g3⟩ := (step_facts hI hx c).reg_keep h1
      refine ⟨g1, h2.trans g3, fun m hm => ?_⟩
      rw [← h3 m hm]
      refine step_frozen hI hx c m (hm.trans h2) ?_
      rcases h0 with h0 | h0
      · exact Or.inl (lt_of_lt_of_le h0 h2)
      · exact Or.inr (by rw [h3 0 (Nat.zero_le _)]; exact h0)
  have hroot := key.2.2 n hn
  refine ⟨hroot, fun hv env env' proven => ?_⟩
  have hv' : ¬ n < cfg.v31Upgrade c := by omega
  unfold finalNodeAccepts getChainBatchRoot
  rw [hroot]
  simp only [hv', if_false]

theorem MigrationSkippedBatchesNeverRecorded :
    Properties.MigrationSkippedBatchesNeverRecorded := by
  intro H cfg s t u env tr c m hs hc hx hrun
  have hI := inv_reachable hs
  have ht : Reachable H cfg t := .step hs hx
  have hx' := hx
  simp only [exec] at hx'
  split_ifs at hx' with h1 h2
  have hsend : env.sender = cfg.chainAssetHandler := not_not.1 h1
  have hcur : t.currentChainBatchNumber c = m := by cases hx'; simp
  have hroots : t.chainBatchRoots = s.chainBatchRoots := by cases hx'; rfl
  have hct : chainRegistered cfg t c = true := by cases hx'; exact hc
  refine ⟨hsend, h2, hcur, ?_, fun n hlo hhi => ?_⟩
  · have := CurrentBatchMonotone H cfg t u tr c ht hrun hct
    omega
  · have hz : s.chainBatchRoots c n = 0 := hI.beyond_zero c n hlo
    obtain ⟨hroot, -⟩ := SettledBatchRootsFrozen H cfg t u tr c n ht hrun hct (by omega)
      (Or.inl (by omega))
    have hu0 : u.chainBatchRoots c n = 0 := by rw [hroot, hroots]; exact hz
    refine ⟨hu0, fun hv env' proven hacc => ?_⟩
    obtain ⟨-, hp, h | ⟨-, hlt, -⟩⟩ := (FinalNodeAcceptsIff cfg env' u c n proven).1 hacc
    · exact hp (h.symm.trans hu0)
    · omega

theorem GenesisSeedOnce : Properties.GenesisSeedOnce := by
  intro H cfg s t tr env c hs hrun h
  simp only [exec]
  rcases h with h | ⟨hc, hpos⟩
  · have h0 : t.chainBatchRoots c 0 ≠ 0 := by
      rw [(BatchRootsWriteOnce H cfg s t tr c 0 hs hrun h).1]; exact h
    simp [h0]
  · have hcur := CurrentBatchMonotone H cfg s t tr c hs hrun hc
    have h0 : t.currentChainBatchNumber c ≠ 0 := by omega
    simp [h0]

theorem ChainWriteProvenance : Properties.ChainWriteProvenance := by
  intro H cfg s t tr c hs hrun hne
  induction hrun with
  | nil => rcases hne with h | h <;> exact absurd rfl h
  | @snoc t' u' tr' e call hr hx ih =>
    by_cases hmid : t'.chainBatchRoots c = s.chainBatchRoots c ∧ t'.chainLeaves c = s.chainLeaves c
    · have hI := inv_reachable (reachable_run hs hr)
      rcases step_writer hI hx c with ⟨g1, _, g3⟩ | g | g
      · rw [g1, g3, hmid.1, hmid.2] at hne
        rcases hne with h | h <;> exact absurd rfl h
      · exact ⟨e, call, List.mem_append_right _ (List.mem_singleton_self _), Or.inl g⟩
      · exact ⟨e, call, List.mem_append_right _ (List.mem_singleton_self _), Or.inr g⟩
    · have hne' : t'.chainBatchRoots c ≠ s.chainBatchRoots c ∨ t'.chainLeaves c ≠ s.chainLeaves c := by
        by_contra hcon
        push Not at hcon
        exact hmid hcon
      obtain ⟨e', call', hm, hw⟩ := ih hne'
      exact ⟨e', call', List.mem_append_left _ hm, hw⟩

theorem LogIdOncePerBlock : Properties.LogIdOncePerBlock := by
  intro H cfg s t tr b hrun hb
  suffices (t.interopRootLogId = s.interopRootLogId
        ∧ (t.lastEmitBlock = s.lastEmitBlock ∨ t.lastEmitBlock = b))
      ∨ (t.interopRootLogId = s.interopRootLogId + 1 ∧ t.lastEmitBlock = b
        ∧ s.lastEmitBlock ≠ b) by
    rcases this with ⟨h1, _⟩ | ⟨h1, _, h3⟩
    · exact ⟨h1.ge, by omega, fun _ => h1⟩
    · exact ⟨by omega, by omega, fun h => absurd h h3⟩
  induction hrun with
  | nil => exact Or.inl ⟨rfl, Or.inl rfl⟩
  | @snoc t' u' tr' e call hr hx ih =>
    have heb : e.blockNumber = b := hb (e, call) (List.mem_append_right _ (List.mem_singleton_self _))
    have ih := ih (fun p hp => hb p (List.mem_append_left _ hp))
    rcases exec_logId hx with ⟨g1, g2⟩ | ⟨g1, g2, g3⟩
    · rw [g1, g2]; exact ih
    · rw [heb] at g1 g2
      by_cases htb : t'.lastEmitBlock = b
      · have := g2 htb.symm
        rcases ih with ⟨h1, _⟩ | ⟨h1, _, h3⟩
        · exact Or.inl ⟨this.trans h1, Or.inr g1⟩
        · exact Or.inr ⟨this.trans h1, g1, h3⟩
      · rcases ih with ⟨h1, h2⟩ | ⟨_, h2, _⟩
        · have hsb : s.lastEmitBlock ≠ b := by
            rcases h2 with h2 | h2
            · rw [← h2]; exact htb
            · exact absurd h2 htb
          rcases g3 with g3 | g3
          · exact Or.inl ⟨g3.trans h1, Or.inr g1⟩
          · exact Or.inr ⟨by rw [g3, h1], g1, hsb⟩
        · exact absurd h2 htb

theorem InteropEnabledOnce : Properties.InteropEnabledOnce := by
  intro H cfg s t tr c hrun
  refine ⟨fun hs => ?_, fun hs ht => ?_, fun env req hs => ?_⟩
  · induction hrun with
    | nil => exact hs
    | @snoc t' u' tr' e call hr hx ih =>
      rcases exec_interop hx with g | ⟨c0, req, _, _, _, _, _, g⟩
      · rw [g]; exact ih
      · rw [g]; by_cases hcc : c = c0
        · subst hcc; simp
        · rw [Function.update_of_ne hcc]; exact ih
  · induction hrun with
    | nil => rw [hs] at ht; cases ht
    | @snoc t' u' tr' e call hr hx ih =>
      by_cases hmid : t'.interopEnabled c = true
      · obtain ⟨e', req, hm, h1, h2, h3⟩ := ih hmid
        exact ⟨e', req, List.mem_append_left _ hm, h1, h2, h3⟩
      · rcases exec_interop hx with g | ⟨c0, req, hcall, h1, h2, _, h4, g⟩
        · rw [g] at ht; exact absurd ht hmid
        · have hcc : c = c0 := by
            by_contra hne; rw [g, Function.update_of_ne hne] at ht; exact hmid ht
          subst hcc; subst hcall
          exact ⟨e, req, List.mem_append_right _ (List.mem_singleton_self _), h1, h2, h4⟩
  · simp only [exec, hs]
    split_ifs <;> rfl

theorem NoReinitialization : Properties.NoReinitialization := by
  intro H cfg s env hs
  have := (inv_reachable hs).initialized
  simp [exec, show ¬ s.initialized < 2 by omega]

end Contracts.MessageRoot
