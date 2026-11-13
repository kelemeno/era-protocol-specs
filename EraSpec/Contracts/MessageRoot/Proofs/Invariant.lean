import EraSpec.Contracts.MessageRoot.Specs.Model
import EraSpec.Contracts.FullMerkle.Proofs.CachedNodes

/-!
# Auxiliary: the storage invariant `Inv` holds after `initialize` and is kept by every call

Lemmas for `Proofs/Model.lean`.  The shape of each internal function's successful result
(`emitRoot_some`, `addNewChainInternal_some`, `recordChainBatchRoot_some`,
`pushChainBatchRoot_some`), then `inv_init` and `inv_exec`.
-/

namespace Contracts.MessageRoot

open Contracts.FullMerkle (FullTree)

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
  · simp [hx, Function.update_of_ne hx]

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
  simp only [exec, fresh, show (0 : ℕ) < 2 by decide, if_true, Option.bind_eq_bind,
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

end Contracts.MessageRoot
