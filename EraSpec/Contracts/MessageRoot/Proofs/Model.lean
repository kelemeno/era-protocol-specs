import EraSpec.Contracts.MessageRoot.Properties.Model
import EraSpec.Contracts.FullMerkle.Proofs.CachedNodes
import EraSpec.Contracts.Merkle.Proofs.RootForgeryPinned

/-!
# Proofs: what the message root guarantees on every run

Each `Properties.X` of `Properties/Model.lean` is proved as `X`.  The file has three parts.

1. **The invariant.**  The shape of each internal function's successful result
   (`emitRoot_some`, `addNewChainInternal_some`, `recordChainBatchRoot_some`,
   `pushChainBatchRoot_some`); `inv_init` (`initialize` on fresh storage establishes `Inv`)
   and `inv_exec` (every successful call keeps it), hence `inv_reachable`.
2. **One step, one chain.**  `step_facts`: on storage satisfying `Inv`, a successful call keeps
   nonzero batch roots and their timestamps, extends each chain tree, keeps registrations,
   indices and slots, does not lower a registered chain's counter, and touches chain `c`'s
   roots, timestamps and tree only when sent by `getZKChain(c)` or the Bridgehub (its counter
   also by the chain asset handler).  `step_writer` names the call; `step_frozen` keeps the
   settled roots; `exec_logId` and `exec_interop` describe the two bookkeeping fields on any
   storage.
3. **The properties**, by induction over `Run` with the step facts.
-/

namespace Contracts.MessageRoot

open AttackVectors.CapacityInvariant (TreeDims)

/-! # Part 1: the invariant -/

/-! ## Shapes of successful internal calls -/

theorem emitRoot_some {env : Env} {s t : State} (h : emitRoot env s = some t) :
    ∃ k, t = { s with interopRootLogId := k, lastEmitBlock := env.blockNumber }
      ∧ (env.blockNumber = s.lastEmitBlock → k = s.interopRootLogId)
      ∧ (k = s.interopRootLogId ∨ k = s.interopRootLogId + 1) := by
  unfold emitRoot at h
  by_cases h1 : env.blockNumber = s.lastEmitBlock
  · simp only [h1, ne_eq, not_true_eq_false, ite_false, Option.some.injEq] at h
    subst h
    refine ⟨s.interopRootLogId, ?_, fun _ => rfl, Or.inl rfl⟩
    cases s; simp_all
  · simp only [h1, ne_eq, not_false_eq_true, ite_true] at h
    split_ifs at h
    cases h
    exact ⟨_, rfl, fun e => absurd e h1, Or.inr rfl⟩

theorem addNewChainInternal_some {H : Hashes} {env : Env} {c start : ℕ} {s t : State}
    (h : addNewChainInternal H env c start s = some t) :
    ∃ S' R k, Contracts.FullMerkle.pushNewLeaf H.node s.sharedTree (H.chainIdLeaf 0 c) = some (S', R)
      ∧ s.chainCount + 1 < UInt256.size
      ∧ (env.blockNumber = s.lastEmitBlock → k = s.interopRootLogId)
      ∧ (k = s.interopRootLogId ∨ k = s.interopRootLogId + 1)
      ∧ t = { s with
          chainCount := s.chainCount + 1
          chainIndex := Function.update s.chainIndex c s.chainCount
          chainIndexToId := Function.update s.chainIndexToId s.chainCount c
          currentChainBatchNumber := Function.update s.currentChainBatchNumber c start
          chainLeaves := Function.update s.chainLeaves c []
          chainTreeSetups := Function.update s.chainTreeSetups c (s.chainTreeSetups c + 1)
          sharedTree := S'
          interopRootLogId := k
          lastEmitBlock := env.blockNumber
          historicalRoots := Function.update s.historicalRoots env.blockNumber (R, env.timestamp) } := by
  unfold addNewChainInternal at h
  split_ifs at h with hk
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨⟨S', R⟩, hp, s₂, he, rfl⟩ := h
    obtain ⟨k, rfl, hk1, hk2⟩ := emitRoot_some he
    exact ⟨S', R, k, hp, hk, hk1, hk2, rfl⟩

theorem recordChainBatchRoot_some {cfg : Config} {c n : ℕ} {r : Bytes32} {s t : State}
    (h : recordChainBatchRoot cfg c n r s = some t) :
    chainRegistered cfg s c = true ∧ r ≠ 0 ∧ s.chainBatchRoots c n = 0
      ∧ s.currentChainBatchNumber c + 1 < UInt256.size
      ∧ n = s.currentChainBatchNumber c + 1
      ∧ t = { s with
          chainBatchRoots := upd2 s.chainBatchRoots c n r
          currentChainBatchNumber := Function.update s.currentChainBatchNumber c n } := by
  unfold recordChainBatchRoot at h
  split_ifs at h with h1 h2 h3 h4 h5
  cases h
  push Not at h3 h4 h5
  subst h5
  exact ⟨by simpa using h1, h2, h3, by omega, rfl, rfl⟩

theorem pushChainBatchRoot_some {H : Hashes} {env : Env} {c n : ℕ} {r : Bytes32} {s t : State}
    (h : pushChainBatchRoot H env c n r s = some t) :
    ∃ S' R k, Contracts.FullMerkle.updateLeaf H.node s.sharedTree (s.chainIndex c)
          (H.chainIdLeaf (chainRootOf H (s.chainLeaves c ++ [H.batchLeaf r n env.timestamp])) c)
          = some (S', R)
      ∧ (env.blockNumber = s.lastEmitBlock → k = s.interopRootLogId)
      ∧ (k = s.interopRootLogId ∨ k = s.interopRootLogId + 1)
      ∧ t = { s with
          chainBatchRootTimestamp := upd2 s.chainBatchRootTimestamp c n env.timestamp
          chainLeaves := Function.update s.chainLeaves c
            (s.chainLeaves c ++ [H.batchLeaf r n env.timestamp])
          sharedTree := S'
          interopRootLogId := k
          lastEmitBlock := env.blockNumber
          historicalRoots := Function.update s.historicalRoots env.blockNumber (R, env.timestamp) } := by
  unfold pushChainBatchRoot at h
  split_ifs at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨⟨S', R⟩, hp, s₃, he, rfl⟩ := h
  obtain ⟨k, rfl, hk1, hk2⟩ := emitRoot_some he
  exact ⟨S', R, k, hp, hk1, hk2, rfl⟩

theorem pushChainBatchRoot_setup {H : Hashes} {env : Env} {c n : ℕ} {r : Bytes32} {s t : State}
    (h : pushChainBatchRoot H env c n r s = some t) : s.chainTreeSetups c ≠ 0 := by
  unfold pushChainBatchRoot at h
  split_ifs at h with h0
  exact h0


/-! ## Small facts -/

theorem upd2_apply {β : Type} (f : ℕ → ℕ → β) (a b : ℕ) (v : β) (x y : ℕ) :
    upd2 f a b v x y = if x = a ∧ y = b then v else f x y := by
  unfold upd2
  by_cases hx : x = a
  · subst hx; by_cases hy : y = b
    · subst hy; simp
    · simp [hy]
  · simp [hx]

theorem chainRegistered_iff {cfg : Config} {s : State} {c : ℕ} :
    chainRegistered cfg s c = true ↔ c = cfg.selfChainId ∨ s.chainIndex c ≠ 0 := by
  simp [chainRegistered]

theorem chainRegistered_false {cfg : Config} {s : State} {c : ℕ} :
    chainRegistered cfg s c = false ↔ c ≠ cfg.selfChainId ∧ s.chainIndex c = 0 := by
  simp [chainRegistered]

variable {H : Hashes} {cfg : Config}

theorem Inv.reg_slot {s : State} {c : ℕ} (hI : Inv H cfg s) (hc : chainRegistered cfg s c = true) :
    s.chainIndex c < s.chainCount ∧ s.chainIndexToId (s.chainIndex c) = c := by
  rcases chainRegistered_iff.1 hc with rfl | h
  · rw [hI.self_index]; exact ⟨hI.count_pos, hI.self_at_zero⟩
  · exact hI.slot_of_index c h

theorem Inv.slot_reg {s : State} {i : ℕ} (hI : Inv H cfg s) (hi : i < s.chainCount) :
    chainRegistered cfg s (s.chainIndexToId i) = true := by
  rw [chainRegistered_iff]
  by_cases h0 : i = 0
  · subst h0; left; exact hI.self_at_zero
  · right; rw [hI.index_of_slot i hi]; exact h0

theorem Inv.slot_ne {s : State} {c i : ℕ} (hI : Inv H cfg s) (hi : i < s.chainCount)
    (hne : i ≠ s.chainIndex c) : s.chainIndexToId i ≠ c := by
  intro h; apply hne; rw [← h, hI.index_of_slot i hi]

theorem sharedLeaves_length (s : State) : (sharedLeaves H s).length = s.chainCount := by
  simp [sharedLeaves]

/-- The witness form of `ChainLog`. -/
def LogWith (H : Hashes) (s : State) (c : ℕ) (ns : List ℕ) : Prop :=
  ns.Pairwise (· < ·)
    ∧ (∀ n ∈ ns, n ≤ s.currentChainBatchNumber c ∧ s.chainBatchRoots c n ≠ 0)
    ∧ s.chainLeaves c = ns.map (batchLeafOf H s c)

theorem logWith_frame {s t : State} {c : ℕ} {ns : List ℕ} (h : LogWith H s c ns)
    (hl : t.chainLeaves c = s.chainLeaves c)
    (hr : ∀ n, s.chainBatchRoots c n ≠ 0 → t.chainBatchRoots c n = s.chainBatchRoots c n
      ∧ t.chainBatchRootTimestamp c n = s.chainBatchRootTimestamp c n)
    (hcur : s.currentChainBatchNumber c ≤ t.currentChainBatchNumber c) : LogWith H t c ns := by
  obtain ⟨hp, hm, hL⟩ := h
  refine ⟨hp, fun n hn => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hm n hn
    exact ⟨h1.trans hcur, by rw [(hr n h2).1]; exact h2⟩
  · rw [hl, hL]
    apply List.map_congr_left
    intro n hn
    obtain ⟨_, h2⟩ := hm n hn
    simp only [batchLeafOf, (hr n h2).1, (hr n h2).2]

theorem chainLog_frame {s t : State} {c : ℕ} (h : ChainLog H s c)
    (hl : t.chainLeaves c = s.chainLeaves c)
    (hr : ∀ n, s.chainBatchRoots c n ≠ 0 → t.chainBatchRoots c n = s.chainBatchRoots c n
      ∧ t.chainBatchRootTimestamp c n = s.chainBatchRootTimestamp c n)
    (hcur : s.currentChainBatchNumber c ≤ t.currentChainBatchNumber c) : ChainLog H t c :=
  let ⟨ns, hns⟩ := h
  ⟨ns, logWith_frame hns hl hr hcur⟩

theorem logWith_push {s t : State} {c n : ℕ} {ns : List ℕ} (h : LogWith H s c ns)
    (hlt : ∀ m ∈ ns, m < n)
    (hl : t.chainLeaves c = s.chainLeaves c ++ [batchLeafOf H t c n])
    (hrn : t.chainBatchRoots c n ≠ 0) (hn : n ≤ t.currentChainBatchNumber c)
    (hcur : s.currentChainBatchNumber c ≤ t.currentChainBatchNumber c)
    (hr : ∀ m, m ≠ n → t.chainBatchRoots c m = s.chainBatchRoots c m
      ∧ t.chainBatchRootTimestamp c m = s.chainBatchRootTimestamp c m) :
    LogWith H t c (ns ++ [n]) := by
  obtain ⟨hp, hm, hL⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [List.pairwise_append]
    refine ⟨hp, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb; subst hb; exact hlt a ha
  · intro m hm'
    rw [List.mem_append] at hm'
    rcases hm' with hm' | hm'
    · have hne : m ≠ n := Nat.ne_of_lt (hlt m hm')
      obtain ⟨a, b⟩ := hm m hm'
      exact ⟨a.trans hcur, by rw [(hr m hne).1]; exact b⟩
    · rw [List.mem_singleton] at hm'; subst hm'; exact ⟨hn, hrn⟩
  · rw [hl, hL, List.map_append, List.map_singleton]
    congr 1
    apply List.map_congr_left
    intro m hm'
    have hne := Nat.ne_of_lt (hlt m hm')
    simp only [batchLeafOf, (hr m hne).1, (hr m hne).2]

/-- A chain whose current batch number is `0` and whose batch-`0` root is empty has an empty
tree. -/
theorem Inv.leaves_nil_of_fresh {s : State} {c : ℕ} (hI : Inv H cfg s)
    (hcur : s.currentChainBatchNumber c = 0) (h0 : s.chainBatchRoots c 0 = 0) :
    s.chainLeaves c = [] := by
  obtain ⟨ns, _, hm, hL⟩ := hI.log c
  have : ns = [] := by
    cases ns with
    | nil => rfl
    | cons m _ =>
      obtain ⟨a, b⟩ := hm m (List.mem_cons_self ..)
      rw [hcur, Nat.le_zero] at a; subst a; exact absurd h0 b
  rw [hL, this, List.map_nil]

theorem sharedLeaves_addNewChain {s t : State} {c : ℕ} (hI : Inv H cfg s)
    (hc : chainRegistered cfg s c = false)
    (ht : t.chainCount = s.chainCount + 1)
    (htoId : t.chainIndexToId = Function.update s.chainIndexToId s.chainCount c)
    (hl : t.chainLeaves = Function.update s.chainLeaves c []) :
    sharedLeaves H t = sharedLeaves H s ++ [H.chainIdLeaf 0 c] := by
  unfold sharedLeaves
  rw [ht, List.range_succ, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    rw [htoId, Function.update_of_ne (Nat.ne_of_lt hi), hl]
    by_cases hci : s.chainIndexToId i = c
    · rw [hci, Function.update_self, (hI.unreg_empty c hc).1]
    · rw [Function.update_of_ne hci]
  · simp [htoId, hl, chainRootOf]

theorem sharedLeaves_set {s t : State} {c : ℕ} {L : List Bytes32} (hI : Inv H cfg s)
    (hc : chainRegistered cfg s c = true)
    (hcount : t.chainCount = s.chainCount) (htoId : t.chainIndexToId = s.chainIndexToId)
    (hl : t.chainLeaves = Function.update s.chainLeaves c L) :
    sharedLeaves H t = (sharedLeaves H s).set (s.chainIndex c) (H.chainIdLeaf (chainRootOf H L) c) := by
  apply List.ext_getElem (by simp [sharedLeaves_length, hcount])
  intro i h1 h2
  rw [List.getElem_set]
  have hi : i < s.chainCount := by rw [sharedLeaves_length] at h1; omega
  split_ifs with hic
  · subst hic
    simp only [sharedLeaves, List.getElem_map, List.getElem_range, htoId, hl,
      (hI.reg_slot hc).2, Function.update_self]
  · have hne : s.chainIndexToId i ≠ c := hI.slot_ne hi (Ne.symm hic)
    simp only [sharedLeaves, List.getElem_map, List.getElem_range, htoId, hl,
      Function.update_of_ne hne]


/-! ## `initialize` establishes the invariant -/

theorem inv_init {env : Env} {s : State} (h : exec H cfg env fresh .initialize = some s) :
    Inv H cfg s := by
  simp only [exec, fresh, show (0 : ℕ) < 2 by decide, ite_true, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at h
  obtain ⟨s₂, h₂, h₃⟩ := h
  split_ifs at h₃
  cases h₃
  obtain ⟨S', R, k, hp, _, _, _, rfl⟩ := addNewChainInternal_some h₂
  have hR0 := (Contracts.FullMerkle.setup_represents_empty H.node cfg.emptyHash).1
  obtain ⟨S'', hp', hR'', -⟩ := Contracts.FullMerkle.pushNewLeaf_computes_root _ _ _ _
    (H.chainIdLeaf 0 cfg.selfChainId) hR0
  simp only [Contracts.FullMerkle.FullTree.empty] at hp hp'
  rw [hp] at hp'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hp')
  have hreach : Contracts.FullMerkle.Reachable H.node cfg.emptyHash S' :=
    .step .init (.push hp)
  refine ⟨le_refl _, by simp, by simp, by simp, ?_, ?_, hreach, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have : i = 0 := by simpa using hi
    subst this; simp
  · intro c hc
    simp only [Function.update_apply] at hc
    split_ifs at hc <;> simp at hc
  · convert hR'' using 1
    simp [sharedLeaves, chainRootOf]
  · intro c _; simp only [Function.update_apply]; split_ifs <;> simp
  · intro c n _; rfl
  · intro c
    refine ⟨[], List.Pairwise.nil, by simp, ?_⟩
    simp only [Function.update_apply]; split_ifs <;> rfl
  · rw [Contracts.FullMerkle.calls_return_the_stored_root _ _ _ S' _ .init
      (Or.inl ⟨_, hp⟩)]
    simp
  · intro c
    by_cases hc : c = cfg.selfChainId
    · subst hc; simp [chainRegistered]
    · simp [chainRegistered, hc]


/-! ## Each call keeps the invariant -/

theorem inv_addNewChain {env : Env} {c start : ℕ} {s t : State} (hI : Inv H cfg s)
    (hc : chainRegistered cfg s c = false) (h : addNewChainInternal H env c start s = some t) :
    Inv H cfg t := by
  obtain ⟨hcs, hc0⟩ := chainRegistered_false.1 hc
  obtain ⟨S', R, k, hp, _, _, _, rfl⟩ := addNewChainInternal_some h
  have hk0 : s.chainCount ≠ 0 := by have := hI.count_pos; omega
  obtain ⟨S'', hp', hR'', -⟩ := Contracts.FullMerkle.pushNewLeaf_computes_root _ _ _ _
    (H.chainIdLeaf 0 c) hI.tree_rep
  rw [hp] at hp'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hp')
  -- `toId i ≠ c` for the old slots
  have hold : ∀ i, i < s.chainCount → s.chainIndexToId i ≠ c := by
    intro i hi hic
    have h1 := hI.index_of_slot i hi
    rw [hic, hc0] at h1
    subst h1
    exact hcs (hic ▸ hI.self_at_zero)
  -- registration in the new state
  have hreg : ∀ c', c' ≠ c → chainRegistered cfg
      { s with chainIndex := Function.update s.chainIndex c s.chainCount } c'
      = chainRegistered cfg s c' := by
    intro c' hne; simp [chainRegistered, Function.update_of_ne hne]
  refine ⟨hI.initialized, by simp, ?_, ?_, ?_, ?_, .step hI.tree_reach (.push hp), ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · simp only [Function.update_of_ne (Ne.symm hk0)]; exact hI.self_at_zero
  · simp only [Function.update_of_ne (Ne.symm hcs)]; exact hI.self_index
  · intro i hi
    simp only [Function.update_apply]
    by_cases hik : i = s.chainCount
    · simp [hik]
    · have hi' : i < s.chainCount := by simp only at hi; omega
      simp [hik, hold i hi', hI.index_of_slot i hi']
  · intro c' hc'
    by_cases hcc : c' = c
    · subst hcc; simp
    · simp only [Function.update_of_ne hcc] at hc' ⊢
      obtain ⟨h1, h2⟩ := hI.slot_of_index c' hc'
      refine ⟨by omega, ?_⟩
      rw [Function.update_of_ne (Nat.ne_of_lt h1)]; exact h2
  · convert hR'' using 1
    exact sharedLeaves_addNewChain hI hc rfl rfl rfl
  · intro c' hc'
    by_cases hcc : c' = c
    · subst hcc; simp [chainRegistered, hk0] at hc'
    · have hc'' : chainRegistered cfg s c' = false := by
        have := hreg c' hcc; simp only [chainRegistered] at this hc' ⊢; rw [← this]; exact hc'
      simp only [Function.update_of_ne hcc]
      exact hI.unreg_empty c' hc''
  · intro c' n hn
    by_cases hcc : c' = c
    · subst hcc; exact (hI.unreg_empty c' hc).2 n
    · simp only [Function.update_of_ne hcc] at hn
      exact hI.beyond_zero c' n hn
  · intro c'
    by_cases hcc : c' = c
    · subst hcc; exact ⟨[], List.Pairwise.nil, by simp, by simp⟩
    · exact chainLog_frame (hI.log c') (by simp [Function.update_of_ne hcc]) (fun _ _ => ⟨rfl, rfl⟩)
        (by simp [Function.update_of_ne hcc])
  · rw [Contracts.FullMerkle.calls_return_the_stored_root _ _ _ _ _ hI.tree_reach (Or.inl ⟨_, hp⟩)]
    simp
  · intro c'
    by_cases hcc : c' = c
    · subst hcc
      have h0 := hI.setups c'
      rw [hc] at h0
      simp [chainRegistered, hk0, h0]
    · have h0 := hI.setups c'
      simp only [chainRegistered, Function.update_of_ne hcc] at h0 ⊢
      exact h0

theorem inv_record {c n : ℕ} {r : Bytes32} {s t : State} (hI : Inv H cfg s)
    (h : recordChainBatchRoot cfg c n r s = some t) : Inv H cfg t := by
  obtain ⟨hc, hr, h0, _, rfl, rfl⟩ := recordChainBatchRoot_some h
  refine ⟨hI.initialized, hI.count_pos, hI.self_at_zero, hI.self_index, hI.index_of_slot,
    hI.slot_of_index, hI.tree_reach, hI.tree_rep, ?_, ?_, ?_, hI.hist, hI.setups⟩
  · intro c' hc'
    have hcc : c' ≠ c := by rintro rfl; simp_all [chainRegistered]
    refine ⟨(hI.unreg_empty c' hc').1, fun m => ?_⟩
    simp only [upd2_apply, hcc, false_and, ite_false]
    exact (hI.unreg_empty c' hc').2 m
  · intro c' m hm
    simp only [upd2_apply]
    split_ifs with hcm
    · obtain ⟨rfl, rfl⟩ := hcm; simp at hm
    · by_cases hcc : c' = c
      · subst hcc
        simp only [Function.update_self] at hm
        exact hI.beyond_zero c' m (by omega)
      · simp only [Function.update_of_ne hcc] at hm
        exact hI.beyond_zero c' m hm
  · intro c'
    refine chainLog_frame (hI.log c') rfl (fun m hm => ⟨?_, rfl⟩) ?_
    · simp only [upd2_apply]
      split_ifs with hcm
      · obtain ⟨rfl, rfl⟩ := hcm; exact absurd h0 hm
      · rfl
    · by_cases hcc : c' = c
      · subst hcc; simp
      · simp [Function.update_of_ne hcc]

/-- `_pushChainBatchRoot` keeps the invariant when the pushed batch is recorded, at most the
current batch number, and above every batch already in the chain's tree. -/
theorem inv_push {env : Env} {c n : ℕ} {s t : State} {ns : List ℕ} (hI : Inv H cfg s)
    (hc : chainRegistered cfg s c = true) (hrn : s.chainBatchRoots c n ≠ 0)
    (hn : n ≤ s.currentChainBatchNumber c) (hlog : LogWith H s c ns) (hlt : ∀ m ∈ ns, m < n)
    (h : pushChainBatchRoot H env c n (s.chainBatchRoots c n) s = some t) : Inv H cfg t := by
  obtain ⟨S', R, k, hp, _, _, rfl⟩ := pushChainBatchRoot_some h
  obtain ⟨hidx, _⟩ := hI.reg_slot hc
  obtain ⟨S'', hp', hR'', -, -⟩ := Contracts.FullMerkle.updateLeaf_computes_root _ _ _ _
    (s.chainIndex c)
    (H.chainIdLeaf (chainRootOf H (s.chainLeaves c ++ [H.batchLeaf (s.chainBatchRoots c n) n
      env.timestamp])) c) hI.tree_rep (by rw [sharedLeaves_length]; exact hidx)
  rw [hp] at hp'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hp')
  refine ⟨hI.initialized, hI.count_pos, hI.self_at_zero, hI.self_index, hI.index_of_slot,
    hI.slot_of_index, .step hI.tree_reach (.update hp), ?_, ?_, hI.beyond_zero, ?_, ?_,
    hI.setups⟩
  · convert hR'' using 1
    exact sharedLeaves_set hI hc rfl rfl rfl
  · intro c' hc'
    have hcc : c' ≠ c := by rintro rfl; simp_all [chainRegistered]
    simp only [Function.update_of_ne hcc]
    exact hI.unreg_empty c' hc'
  · intro c'
    by_cases hcc : c' = c
    · subst hcc
      refine ⟨ns ++ [n], logWith_push hlog hlt ?_ hrn hn le_rfl ?_⟩
      · simp [batchLeafOf, upd2_apply]
      · intro m hm; simp [upd2_apply, hm]
    · refine chainLog_frame (hI.log c') (by simp [Function.update_of_ne hcc])
        (fun m _ => ⟨rfl, by simp [upd2_apply, hcc]⟩) le_rfl
  · rw [Contracts.FullMerkle.calls_return_the_stored_root _ _ _ _ _ hI.tree_reach
      (Or.inr ⟨_, _, hp⟩)]
    simp

theorem inv_exec {env : Env} {call : Call} {s t : State} (hI : Inv H cfg s)
    (h : exec H cfg env s call = some t) : Inv H cfg t := by
  cases call with
  | «initialize» =>
    have := hI.initialized
    simp [exec, show ¬ s.initialized < 2 by omega] at h
  | addNewChain c start =>
    simp only [exec] at h
    split_ifs at h with h1 h2
    exact inv_addNewChain hI (by simpa using h2) h
  | setMigratingChainBatchNumber c n =>
    simp only [exec] at h
    split_ifs at h with h1 h2
    cases h
    refine ⟨hI.initialized, hI.count_pos, hI.self_at_zero, hI.self_index, hI.index_of_slot,
      hI.slot_of_index, hI.tree_reach, hI.tree_rep, hI.unreg_empty, ?_, ?_, hI.hist, hI.setups⟩
    · intro c' m hm
      by_cases hcc : c' = c
      · subst hcc; simp only [Function.update_self] at hm
        exact hI.beyond_zero c' m (by omega)
      · simp only [Function.update_of_ne hcc] at hm; exact hI.beyond_zero c' m hm
    · intro c'
      refine chainLog_frame (hI.log c') rfl (fun _ _ => ⟨rfl, rfl⟩) ?_
      by_cases hcc : c' = c
      · subst hcc; simpa using h2
      · simp [Function.update_of_ne hcc]
  | addChainBatchRoot c n r =>
    simp only [exec] at h
    split_ifs at h
    exact inv_record hI h
  | addChainBatchRootV32 c n r =>
    simp only [exec] at h
    split_ifs at h
    obtain ⟨s₁, h₁, h₂⟩ : ∃ s₁, recordChainBatchRoot cfg c n r s = some s₁
        ∧ pushChainBatchRoot H env c n r s₁ = some t := by
      cases hrec : recordChainBatchRoot cfg c n r s with
      | none => rw [hrec] at h; cases h
      | some s₁ => rw [hrec] at h; exact ⟨s₁, rfl, h⟩
    have hI₁ := inv_record hI h₁
    obtain ⟨hc, hr, h0, _, hn, rfl⟩ := recordChainBatchRoot_some h₁
    obtain ⟨ns, hlog⟩ := hI.log c
    have hlt : ∀ m ∈ ns, m < n := fun m hm => by have := (hlog.2.1 m hm).1; omega
    refine inv_push (c := c) (n := n) hI₁ (by simpa [chainRegistered] using hc)
      (by simp [upd2_apply, hr])
      (by simp) (logWith_frame hlog rfl ?_ (by simp; omega)) hlt (by simpa [upd2_apply] using h₂)
    intro m hm
    refine ⟨?_, rfl⟩
    simp only [upd2_apply]
    split_ifs with hcm
    · obtain ⟨-, rfl⟩ := hcm; exact absurd h0 hm
    · rfl
  | seedGenesisRoot c =>
    simp only [exec] at h
    split_ifs at h with h1 h2 h3 h4 h5
    push Not at h1 h2 h4 h5
    have hc : chainRegistered cfg s c = true := by simpa using h3
    have hnil := hI.leaves_nil_of_fresh h4 h5
    -- the state after `chainBatchRoots[c][0] = g`
    have hI₁ : Inv H cfg
        { s with chainBatchRoots := (upd2 s.chainBatchRoots c 0 (env.l2LogsRootHash c 0)) } := by
      refine ⟨hI.initialized, hI.count_pos, hI.self_at_zero, hI.self_index, hI.index_of_slot,
        hI.slot_of_index, hI.tree_reach, hI.tree_rep, ?_, ?_, ?_, hI.hist, hI.setups⟩
      · intro c' hc'
        have hcc : c' ≠ c := by rintro rfl; simp_all [chainRegistered]
        exact ⟨(hI.unreg_empty c' hc').1, fun m => by
          simp only [upd2_apply, hcc, false_and, ite_false]; exact (hI.unreg_empty c' hc').2 m⟩
      · intro c' m hm
        simp only [upd2_apply]
        split_ifs with hcm
        · obtain ⟨rfl, rfl⟩ := hcm; simp at hm
        · exact hI.beyond_zero c' m hm
      · intro c'
        by_cases hcc : c' = c
        · subst hcc; exact ⟨[], List.Pairwise.nil, by simp, hnil⟩
        · exact chainLog_frame (hI.log c') rfl
            (fun m _ => ⟨by simp [upd2_apply, hcc], rfl⟩) le_rfl
    refine inv_push (c := c) (n := 0) hI₁ (by simpa [chainRegistered] using hc)
      (by simp [upd2_apply, h2])
      (by simp) (ns := []) ⟨List.Pairwise.nil, by simp, by simpa using hnil⟩ (by simp)
      (by simpa [upd2_apply] using h)
  | enableInterop c req =>
    simp only [exec] at h
    split_ifs at h
    cases h
    exact ⟨hI.initialized, hI.count_pos, hI.self_at_zero, hI.self_index, hI.index_of_slot,
      hI.slot_of_index, hI.tree_reach, hI.tree_rep, hI.unreg_empty, hI.beyond_zero, hI.log,
      hI.hist, hI.setups⟩

theorem inv_reachable {s : State} (h : Reachable H cfg s) : Inv H cfg s := by
  induction h with
  | init h => exact inv_init h
  | step _ h ih => exact inv_exec ih h

theorem reachable_run {s t : State} {tr : List (Env × Call)} (hs : Reachable H cfg s)
    (h : Run H cfg s tr t) : Reachable H cfg t := by
  induction h with
  | nil => exact hs
  | snoc _ h ih => exact .step ih h


/-! # Part 2: what one successful call does to one chain -/

/-- The per-chain facts of one step. -/
structure StepFacts (cfg : Config) (env : Env) (s t : State) (c : ℕ) : Prop where
  roots_once : ∀ n, s.chainBatchRoots c n ≠ 0 →
    t.chainBatchRoots c n = s.chainBatchRoots c n
      ∧ t.chainBatchRootTimestamp c n = s.chainBatchRootTimestamp c n
  leaves_prefix : s.chainLeaves c <+: t.chainLeaves c
  reg_keep : chainRegistered cfg s c = true →
    chainRegistered cfg t c = true ∧ t.chainIndex c = s.chainIndex c
      ∧ s.currentChainBatchNumber c ≤ t.currentChainBatchNumber c
  writers : env.sender ≠ env.zkChain c → env.sender ≠ cfg.bridgehub →
    t.chainBatchRoots c = s.chainBatchRoots c
      ∧ t.chainBatchRootTimestamp c = s.chainBatchRootTimestamp c
      ∧ t.chainLeaves c = s.chainLeaves c
      ∧ (env.sender ≠ cfg.chainAssetHandler →
          t.currentChainBatchNumber c = s.currentChainBatchNumber c)
  count_le : s.chainCount ≤ t.chainCount
  slots_keep : ∀ i, i < s.chainCount → t.chainIndexToId i = s.chainIndexToId i

/-- The push half of a batch append, as one `StepFacts`-shaped fact about chain `c`. -/
theorem push_facts {env : Env} {c0 n : ℕ} {r : Bytes32} {s t : State} (c : ℕ)
    (h : pushChainBatchRoot H env c0 n r s = some t) :
    t.chainBatchRoots = s.chainBatchRoots
      ∧ t.currentChainBatchNumber = s.currentChainBatchNumber
      ∧ t.chainIndex = s.chainIndex ∧ t.chainCount = s.chainCount
      ∧ t.chainIndexToId = s.chainIndexToId
      ∧ t.chainBatchRootTimestamp = upd2 s.chainBatchRootTimestamp c0 n env.timestamp
      ∧ t.chainLeaves c = (if c = c0 then s.chainLeaves c ++ [H.batchLeaf r n env.timestamp]
          else s.chainLeaves c) := by
  obtain ⟨S', R, k, _, _, _, rfl⟩ := pushChainBatchRoot_some h
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  by_cases hc : c = c0
  · subst hc; simp
  · simp [hc]

theorem step_facts {env : Env} {call : Call} {s t : State} (hI : Inv H cfg s)
    (h : exec H cfg env s call = some t) (c : ℕ) : StepFacts cfg env s t c := by
  cases call with
  | «initialize» =>
    have := hI.initialized
    simp [exec, show ¬ s.initialized < 2 by omega] at h
  | addNewChain c0 start =>
    simp only [exec] at h
    split_ifs at h with h1 h2
    have hc0 : chainRegistered cfg s c0 = false := by simpa using h2
    obtain ⟨hcs, hidx⟩ := chainRegistered_false.1 hc0
    obtain ⟨S', R, k, _, _, _, _, rfl⟩ := addNewChainInternal_some h
    have hk0 : s.chainCount ≠ 0 := by have := hI.count_pos; omega
    have hleaves : (Function.update s.chainLeaves c0 [] c) = s.chainLeaves c := by
      by_cases hcc : c = c0
      · subst hcc; rw [Function.update_self, (hI.unreg_empty c hc0).1]
      · rw [Function.update_of_ne hcc]
    refine ⟨fun _ _ => ⟨rfl, rfl⟩, by simp only [hleaves]; exact List.prefix_refl _, ?_, ?_,
      by simp, ?_⟩
    · intro hc
      have hcc : c ≠ c0 := by rintro rfl; rw [hc] at hc0; cases hc0
      refine ⟨?_, by simp [Function.update_of_ne hcc], by simp [Function.update_of_ne hcc]⟩
      simp only [chainRegistered, Function.update_of_ne hcc]; exact hc
    · intro _ hbh
      refine ⟨rfl, rfl, hleaves, fun hcah => ?_⟩
      push Not at h1
      exact absurd (h1 hbh) hcah
    · intro i hi
      simp [Function.update_of_ne (Nat.ne_of_lt hi)]
  | setMigratingChainBatchNumber c0 n =>
    simp only [exec] at h
    split_ifs at h with h1 h2
    cases h
    push Not at h1
    refine ⟨fun _ _ => ⟨rfl, rfl⟩, List.prefix_refl _, fun hc => ⟨hc, rfl, ?_⟩,
      fun _ _ => ⟨rfl, rfl, rfl, fun hcah => absurd h1 hcah⟩, le_rfl, fun _ _ => rfl⟩
    by_cases hcc : c = c0
    · subst hcc; simpa using h2
    · simp [Function.update_of_ne hcc]
  | addChainBatchRoot c0 n r =>
    simp only [exec] at h
    split_ifs at h with h1
    push Not at h1
    obtain ⟨hc0, hr, h0, _, hn, rfl⟩ := recordChainBatchRoot_some h
    refine ⟨fun m hm => ⟨?_, rfl⟩, List.prefix_refl _, fun hc => ⟨hc, rfl, ?_⟩, ?_, le_rfl,
      fun _ _ => rfl⟩
    · simp only [upd2_apply]; split_ifs with hcm
      · obtain ⟨rfl, rfl⟩ := hcm; exact absurd h0 hm
      · rfl
    · by_cases hcc : c = c0
      · subst hcc; simp; omega
      · simp [Function.update_of_ne hcc]
    · intro hz _
      have hcc : c ≠ c0 := by rintro rfl; exact hz h1
      refine ⟨?_, rfl, rfl, fun _ => by simp [Function.update_of_ne hcc]⟩
      funext m; simp [upd2_apply, hcc]
  | addChainBatchRootV32 c0 n r =>
    simp only [exec] at h
    split_ifs at h with h1
    push Not at h1
    obtain ⟨s₁, h₁, h₂⟩ : ∃ s₁, recordChainBatchRoot cfg c0 n r s = some s₁
        ∧ pushChainBatchRoot H env c0 n r s₁ = some t := by
      cases hrec : recordChainBatchRoot cfg c0 n r s with
      | none => rw [hrec] at h; cases h
      | some s₁ => rw [hrec] at h; exact ⟨s₁, rfl, h⟩
    obtain ⟨hc0, hr, h0, _, hn, rfl⟩ := recordChainBatchRoot_some h₁
    obtain ⟨er, ec, ei, ek, eto, ets, el⟩ := push_facts c h₂
    simp only at er ec ei ek eto
    refine ⟨fun m hm => ⟨?_, ?_⟩, ?_, fun hc => ⟨?_, by rw [ei], ?_⟩, ?_, by rw [ek],
      fun _ _ => by rw [eto]⟩
    · rw [er]; simp only [upd2_apply]; split_ifs with hcm
      · obtain ⟨rfl, rfl⟩ := hcm; exact absurd h0 hm
      · rfl
    · rw [ets]; simp only [upd2_apply]; split_ifs with hcm
      · obtain ⟨rfl, rfl⟩ := hcm; exact absurd h0 hm
      · rfl
    · rw [el]; split_ifs
      · exact List.prefix_append _ _
      · exact List.prefix_refl _
    · simp only [chainRegistered, ei]; simpa [chainRegistered] using hc
    · rw [ec]; by_cases hcc : c = c0
      · subst hcc; simp; omega
      · simp [Function.update_of_ne hcc]
    · intro hz _
      have hcc : c ≠ c0 := by rintro rfl; exact hz h1
      refine ⟨?_, ?_, by rw [el]; simp [hcc], fun _ => by rw [ec]; simp [Function.update_of_ne hcc]⟩
      · rw [er]; funext m; simp [upd2_apply, hcc]
      · rw [ets]; funext m; simp [upd2_apply, hcc]
  | seedGenesisRoot c0 =>
    simp only [exec] at h
    split_ifs at h with h1 h2 h3 h4 h5
    push Not at h1 h2 h4 h5
    obtain ⟨er, ec, ei, ek, eto, ets, el⟩ := push_facts c h
    simp only at er ec ei ek eto
    refine ⟨fun m hm => ⟨?_, ?_⟩, ?_, fun hc => ⟨?_, by rw [ei], by rw [ec]⟩,
      fun _ hbh => absurd h1 hbh, by rw [ek], fun _ _ => by rw [eto]⟩
    · rw [er]; simp only [upd2_apply]; split_ifs with hcm
      · obtain ⟨rfl, rfl⟩ := hcm; exact absurd h5 hm
      · rfl
    · rw [ets]; simp only [upd2_apply]; split_ifs with hcm
      · obtain ⟨rfl, rfl⟩ := hcm; exact absurd h5 hm
      · rfl
    · rw [el]; split_ifs
      · exact List.prefix_append _ _
      · exact List.prefix_refl _
    · simp only [chainRegistered, ei]; simpa [chainRegistered] using hc
  | enableInterop c0 req =>
    simp only [exec] at h
    split_ifs at h
    cases h
    exact ⟨fun _ _ => ⟨rfl, rfl⟩, List.prefix_refl _, fun hc => ⟨hc, rfl, le_rfl⟩,
      fun _ _ => ⟨rfl, rfl, rfl, fun _ => rfl⟩, le_rfl, fun _ _ => rfl⟩

/-- One successful call either leaves chain `c`'s batch roots, timestamps and tree alone, or is
an append for `c` sent by `getZKChain(c)`, or is `seedGenesisRoot(c)` sent by the Bridgehub. -/
theorem step_writer {env : Env} {call : Call} {s t : State} (hI : Inv H cfg s)
    (h : exec H cfg env s call = some t) (c : ℕ) :
    (t.chainBatchRoots c = s.chainBatchRoots c
        ∧ t.chainBatchRootTimestamp c = s.chainBatchRootTimestamp c
        ∧ t.chainLeaves c = s.chainLeaves c)
      ∨ (env.sender = env.zkChain c
          ∧ ∃ n r, call = .addChainBatchRoot c n r ∨ call = .addChainBatchRootV32 c n r)
      ∨ (env.sender = cfg.bridgehub ∧ call = .seedGenesisRoot c) := by
  cases call with
  | «initialize» =>
    have := hI.initialized
    simp [exec, show ¬ s.initialized < 2 by omega] at h
  | addNewChain c0 start =>
    simp only [exec] at h
    split_ifs at h with h1 h2
    have hc0 : chainRegistered cfg s c0 = false := by simpa using h2
    obtain ⟨S', R, k, _, _, _, _, rfl⟩ := addNewChainInternal_some h
    refine Or.inl ⟨rfl, rfl, ?_⟩
    by_cases hcc : c = c0
    · subst hcc; simp [(hI.unreg_empty c hc0).1]
    · simp [Function.update_of_ne hcc]
  | setMigratingChainBatchNumber c0 n =>
    simp only [exec] at h
    split_ifs at h
    cases h
    exact Or.inl ⟨rfl, rfl, rfl⟩
  | addChainBatchRoot c0 n r =>
    simp only [exec] at h
    split_ifs at h with h1
    push Not at h1
    obtain ⟨_, _, _, _, _, rfl⟩ := recordChainBatchRoot_some h
    by_cases hcc : c = c0
    · subst hcc; exact Or.inr (Or.inl ⟨h1, n, r, Or.inl rfl⟩)
    · refine Or.inl ⟨?_, rfl, rfl⟩
      funext m; simp [upd2_apply, hcc]
  | addChainBatchRootV32 c0 n r =>
    simp only [exec] at h
    split_ifs at h with h1
    push Not at h1
    by_cases hcc : c = c0
    · subst hcc; exact Or.inr (Or.inl ⟨h1, n, r, Or.inr rfl⟩)
    · obtain ⟨s₁, h₁, h₂⟩ : ∃ s₁, recordChainBatchRoot cfg c0 n r s = some s₁
          ∧ pushChainBatchRoot H env c0 n r s₁ = some t := by
        cases hrec : recordChainBatchRoot cfg c0 n r s with
        | none => rw [hrec] at h; cases h
        | some s₁ => rw [hrec] at h; exact ⟨s₁, rfl, h⟩
      obtain ⟨_, _, _, _, _, rfl⟩ := recordChainBatchRoot_some h₁
      obtain ⟨er, _, _, _, _, ets, el⟩ := push_facts c h₂
      refine Or.inl ⟨?_, ?_, by rw [el]; simp [hcc]⟩
      · rw [er]; funext m; simp [upd2_apply, hcc]
      · rw [ets]; funext m; simp [upd2_apply, hcc]
  | seedGenesisRoot c0 =>
    simp only [exec] at h
    split_ifs at h with h1
    push Not at h1
    by_cases hcc : c = c0
    · subst hcc; exact Or.inr (Or.inr ⟨h1, rfl⟩)
    · obtain ⟨er, _, _, _, _, ets, el⟩ := push_facts c h
      refine Or.inl ⟨?_, ?_, by rw [el]; simp [hcc]⟩
      · rw [er]; funext m; simp [upd2_apply, hcc]
      · rw [ets]; funext m; simp [upd2_apply, hcc]
  | enableInterop c0 req =>
    simp only [exec] at h
    split_ifs at h
    cases h
    exact Or.inl ⟨rfl, rfl, rfl⟩

/-- One successful call does not change `chainBatchRoots[c][n]` for `n` at or below the chain's
counter, once the counter is positive or the genesis root is recorded. -/
theorem step_frozen {env : Env} {call : Call} {s t : State} (hI : Inv H cfg s)
    (h : exec H cfg env s call = some t) (c n : ℕ) (hn : n ≤ s.currentChainBatchNumber c)
    (h0 : 0 < s.currentChainBatchNumber c ∨ s.chainBatchRoots c 0 ≠ 0) :
    t.chainBatchRoots c n = s.chainBatchRoots c n := by
  cases call with
  | «initialize» =>
    have := hI.initialized
    simp [exec, show ¬ s.initialized < 2 by omega] at h
  | addNewChain c0 start =>
    simp only [exec] at h
    split_ifs at h
    obtain ⟨S', R, k, _, _, _, _, rfl⟩ := addNewChainInternal_some h
    rfl
  | setMigratingChainBatchNumber c0 m =>
    simp only [exec] at h
    split_ifs at h
    cases h
    rfl
  | addChainBatchRoot c0 m r =>
    simp only [exec] at h
    split_ifs at h
    obtain ⟨_, _, _, _, hm, rfl⟩ := recordChainBatchRoot_some h
    simp only [upd2_apply]
    split_ifs with hcm
    · obtain ⟨rfl, rfl⟩ := hcm; omega
    · rfl
  | addChainBatchRootV32 c0 m r =>
    simp only [exec] at h
    split_ifs at h
    obtain ⟨s₁, h₁, h₂⟩ : ∃ s₁, recordChainBatchRoot cfg c0 m r s = some s₁
        ∧ pushChainBatchRoot H env c0 m r s₁ = some t := by
      cases hrec : recordChainBatchRoot cfg c0 m r s with
      | none => rw [hrec] at h; cases h
      | some s₁ => rw [hrec] at h; exact ⟨s₁, rfl, h⟩
    obtain ⟨_, _, _, _, hm, rfl⟩ := recordChainBatchRoot_some h₁
    obtain ⟨er, _⟩ := push_facts c h₂
    rw [er]
    simp only [upd2_apply]
    split_ifs with hcm
    · obtain ⟨rfl, rfl⟩ := hcm; omega
    · rfl
  | seedGenesisRoot c0 =>
    simp only [exec] at h
    split_ifs at h with h1 h2 h3 h4 h5
    push Not at h4 h5
    obtain ⟨er, _⟩ := push_facts c h
    rw [er]
    simp only [upd2_apply]
    split_ifs with hcm
    · obtain ⟨rfl, rfl⟩ := hcm
      rcases h0 with h0 | h0
      · omega
      · exact absurd h5 h0
    · rfl
  | enableInterop c0 req =>
    simp only [exec] at h
    split_ifs at h
    cases h
    rfl

/-! ## The two bookkeeping fields, on any storage -/

theorem exec_logId {env : Env} {call : Call} {s t : State} (h : exec H cfg env s call = some t) :
    (t.interopRootLogId = s.interopRootLogId ∧ t.lastEmitBlock = s.lastEmitBlock)
      ∨ (t.lastEmitBlock = env.blockNumber
        ∧ (env.blockNumber = s.lastEmitBlock → t.interopRootLogId = s.interopRootLogId)
        ∧ (t.interopRootLogId = s.interopRootLogId
          ∨ t.interopRootLogId = s.interopRootLogId + 1)) := by
  cases call with
  | «initialize» =>
    simp only [exec, Option.bind_eq_bind] at h
    split_ifs at h
    all_goals try (simp at h; done)
    obtain ⟨s₂, h₂, h₃⟩ := Option.bind_eq_some_iff.1 h
    cases h₃
    obtain ⟨S', R, k, _, _, hk1, hk2, rfl⟩ := addNewChainInternal_some h₂
    exact Or.inr ⟨rfl, hk1, hk2⟩
  | addNewChain c0 start =>
    simp only [exec] at h
    split_ifs at h
    obtain ⟨S', R, k, _, _, hk1, hk2, rfl⟩ := addNewChainInternal_some h
    exact Or.inr ⟨rfl, hk1, hk2⟩
  | setMigratingChainBatchNumber c0 n =>
    simp only [exec] at h
    split_ifs at h
    cases h
    exact Or.inl ⟨rfl, rfl⟩
  | addChainBatchRoot c0 n r =>
    simp only [exec] at h
    split_ifs at h
    obtain ⟨_, _, _, _, _, rfl⟩ := recordChainBatchRoot_some h
    exact Or.inl ⟨rfl, rfl⟩
  | addChainBatchRootV32 c0 n r =>
    simp only [exec] at h
    split_ifs at h
    obtain ⟨s₁, h₁, h₂⟩ : ∃ s₁, recordChainBatchRoot cfg c0 n r s = some s₁
        ∧ pushChainBatchRoot H env c0 n r s₁ = some t := by
      cases hrec : recordChainBatchRoot cfg c0 n r s with
      | none => rw [hrec] at h; cases h
      | some s₁ => rw [hrec] at h; exact ⟨s₁, rfl, h⟩
    obtain ⟨_, _, _, _, _, rfl⟩ := recordChainBatchRoot_some h₁
    obtain ⟨S', R, k, _, hk1, hk2, rfl⟩ := pushChainBatchRoot_some h₂
    exact Or.inr ⟨rfl, hk1, hk2⟩
  | seedGenesisRoot c0 =>
    simp only [exec] at h
    split_ifs at h
    obtain ⟨S', R, k, _, hk1, hk2, rfl⟩ := pushChainBatchRoot_some h
    exact Or.inr ⟨rfl, hk1, hk2⟩
  | enableInterop c0 req =>
    simp only [exec] at h
    split_ifs at h
    cases h
    exact Or.inl ⟨rfl, rfl⟩

theorem exec_interop {env : Env} {call : Call} {s t : State}
    (h : exec H cfg env s call = some t) :
    t.interopEnabled = s.interopEnabled
      ∨ ∃ c0 req, call = .enableInterop c0 req ∧ env.sender = env.bridgehubOwner
        ∧ env.zkChain c0 ≠ 0 ∧ s.interopEnabled c0 = false ∧ env.backfillPending c0 = false
        ∧ t.interopEnabled = Function.update s.interopEnabled c0 true := by
  cases call with
  | «initialize» =>
    simp only [exec, Option.bind_eq_bind] at h
    split_ifs at h
    all_goals try (simp at h; done)
    obtain ⟨s₂, h₂, h₃⟩ := Option.bind_eq_some_iff.1 h
    cases h₃
    obtain ⟨S', R, k, _, _, _, _, rfl⟩ := addNewChainInternal_some h₂
    exact Or.inl rfl
  | addNewChain c0 start =>
    simp only [exec] at h
    split_ifs at h
    obtain ⟨S', R, k, _, _, _, _, rfl⟩ := addNewChainInternal_some h
    exact Or.inl rfl
  | setMigratingChainBatchNumber c0 n =>
    simp only [exec] at h
    split_ifs at h
    cases h
    exact Or.inl rfl
  | addChainBatchRoot c0 n r =>
    simp only [exec] at h
    split_ifs at h
    obtain ⟨_, _, _, _, _, rfl⟩ := recordChainBatchRoot_some h
    exact Or.inl rfl
  | addChainBatchRootV32 c0 n r =>
    simp only [exec] at h
    split_ifs at h
    obtain ⟨s₁, h₁, h₂⟩ : ∃ s₁, recordChainBatchRoot cfg c0 n r s = some s₁
        ∧ pushChainBatchRoot H env c0 n r s₁ = some t := by
      cases hrec : recordChainBatchRoot cfg c0 n r s with
      | none => rw [hrec] at h; cases h
      | some s₁ => rw [hrec] at h; exact ⟨s₁, rfl, h⟩
    obtain ⟨_, _, _, _, _, rfl⟩ := recordChainBatchRoot_some h₁
    obtain ⟨S', R, k, _, _, _, rfl⟩ := pushChainBatchRoot_some h₂
    exact Or.inl rfl
  | seedGenesisRoot c0 =>
    simp only [exec] at h
    split_ifs at h
    obtain ⟨S', R, k, _, _, _, rfl⟩ := pushChainBatchRoot_some h
    exact Or.inl rfl
  | enableInterop c0 req =>
    simp only [exec] at h
    split_ifs at h with h1 h2 h3 h4
    cases h
    push Not at h1 h2
    refine Or.inr ⟨c0, req, rfl, h1, h2, by simpa using h3, by simpa using h4, rfl⟩


/-! # Part 3: the properties -/

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
  rw [ite_eq_right hcount, Contracts.FullMerkle.root_is_fold _ _ _ _ hI.tree_rep, hH, hnum]

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
  rw [ite_eq_right hcount, hI.hist]

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
    rw [ite_eq_right (by simp [hc]), ite_eq_right hr, ite_eq_right (by simp [h0]), ite_eq_right hof', ite_eq_right (by omega)]
  obtain ⟨hidx, _⟩ := hI.reg_slot hc
  obtain ⟨S'', hp, -, -, -⟩ := Contracts.FullMerkle.updateLeaf_computes_root _ _ _ _
    (s.chainIndex c)
    (H.chainIdLeaf (chainRootOf H (s.chainLeaves c ++ [H.batchLeaf r n env.timestamp])) c)
    hI.tree_rep (by rw [sharedLeaves_length]; exact hidx)
  apply Option.isSome_iff_exists.1
  simp only [exec, hsend, ne_eq, not_true_eq_false, ite_false, hrec, Option.bind_some]
  have hset : s.chainTreeSetups c ≠ 0 := by simp [hI.setups c, hc]
  unfold pushChainBatchRoot
  simp only [hset, ite_false, Option.bind_eq_bind, Option.pure_def, hp, Option.bind_some]
  exact emitRoot_bind_isSome _ hlog

theorem AddNewChainLiveness : Properties.AddNewChainLiveness := by
  intro H cfg s env c start hs hsend hc hcount hlog
  have hI := inv_reachable hs
  obtain ⟨S', hp, -, -⟩ := Contracts.FullMerkle.pushNewLeaf_computes_root _ _ _ _
    (H.chainIdLeaf 0 c) hI.tree_rep
  have hguard : ¬ (env.sender ≠ cfg.bridgehub ∧ env.sender ≠ cfg.chainAssetHandler) := by tauto
  apply Option.isSome_iff_exists.1
  simp only [exec, hguard, ite_false, hc, Bool.false_eq_true]
  unfold addNewChainInternal
  simp only [hcount, ite_true, Option.bind_eq_bind, Option.pure_def, hp, Option.bind_some]
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
    · rw [ite_eq_right hn0, ite_eq_right (by simpa using hr), ite_eq_right (by omega)] at h
      simp at h
    · rw [ite_eq_right hn0, ite_eq_left hr] at h
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
    rw [ite_eq_right hn0]
    by_cases hr : s.chainBatchRoots c n = 0
    · rw [ite_eq_right (not_not.2 hr)]
      by_cases hv : n < cfg.v31Upgrade c
      · rw [ite_eq_left hv]
        simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨hpos, h1 ▸ h2, Or.inr ⟨hr, hv, h1⟩⟩
        · rintro ⟨-, h1, h2 | ⟨-, -, h2⟩⟩
          · exact absurd (h2.symm.trans hr) h1
          · exact ⟨h2, h2 ▸ h1⟩
      · rw [ite_eq_right hv]
        simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨-, h2⟩; exact absurd rfl h2
        · rintro ⟨-, h1, h2 | ⟨-, h2, -⟩⟩
          · exact absurd (h2.symm.trans hr) h1
          · exact absurd h2 hv
    · rw [ite_eq_left hr]
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
  simp only [hv', ite_false]

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
