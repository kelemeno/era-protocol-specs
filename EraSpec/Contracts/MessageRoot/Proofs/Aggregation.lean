import EraSpec.Contracts.MessageRoot.Properties.Aggregation

namespace Contracts.MessageRoot

/-! ## Field lemmas for the effects -/

section fields
variable (P : Params) (st : State) (c : ChainId) (s b : ℕ) (r : Word) (τ : ℕ)

@[simp] theorem addChain_block : (st.addChain P c s).block = st.block := rfl
@[simp] theorem addChain_time : (st.addChain P c s).time = st.time := rfl
@[simp] theorem addChain_chainCount : (st.addChain P c s).chainCount = st.chainCount + 1 := rfl
@[simp] theorem addChain_chainIndex :
    (st.addChain P c s).chainIndex = Function.update st.chainIndex c st.chainCount := rfl
@[simp] theorem addChain_chainIndexToId :
    (st.addChain P c s).chainIndexToId = Function.update st.chainIndexToId st.chainCount c := rfl
@[simp] theorem addChain_current :
    (st.addChain P c s).current = Function.update st.current c s := rfl
@[simp] theorem addChain_batchRoot : (st.addChain P c s).batchRoot = st.batchRoot := rfl
@[simp] theorem addChain_batchTs : (st.addChain P c s).batchTs = st.batchTs := rfl
@[simp] theorem addChain_leaves :
    (st.addChain P c s).leaves = Function.update st.leaves c [] := rfl
@[simp] theorem addChain_shared :
    (st.addChain P c s).shared = st.shared ++ [P.H.chainIdLeaf 0 c] := rfl
@[simp] theorem addChain_hist :
    (st.addChain P c s).hist = Function.update st.hist st.block
      (some ⟨P.H.sharedRoot (st.shared ++ [P.H.chainIdLeaf 0 c]), st.time,
        fun c' => (Function.update st.leaves c [] c').length⟩) := rfl

@[simp] theorem setBatchRoot_block : (st.setBatchRoot c b r).block = st.block := rfl
@[simp] theorem setBatchRoot_time : (st.setBatchRoot c b r).time = st.time := rfl
@[simp] theorem setBatchRoot_chainCount : (st.setBatchRoot c b r).chainCount = st.chainCount := rfl
@[simp] theorem setBatchRoot_chainIndex : (st.setBatchRoot c b r).chainIndex = st.chainIndex := rfl
@[simp] theorem setBatchRoot_chainIndexToId :
    (st.setBatchRoot c b r).chainIndexToId = st.chainIndexToId := rfl
@[simp] theorem setBatchRoot_current : (st.setBatchRoot c b r).current = st.current := rfl
@[simp] theorem setBatchRoot_batchRoot :
    (st.setBatchRoot c b r).batchRoot =
      Function.update st.batchRoot c (Function.update (st.batchRoot c) b r) := rfl
@[simp] theorem setBatchRoot_batchTs : (st.setBatchRoot c b r).batchTs = st.batchTs := rfl
@[simp] theorem setBatchRoot_leaves : (st.setBatchRoot c b r).leaves = st.leaves := rfl
@[simp] theorem setBatchRoot_shared : (st.setBatchRoot c b r).shared = st.shared := rfl
@[simp] theorem setBatchRoot_hist : (st.setBatchRoot c b r).hist = st.hist := rfl
@[simp] theorem setBatchRoot_newLeaf :
    (st.setBatchRoot c b r).newLeaf = st.newLeaf := rfl

@[simp] theorem record_block : (st.record c b r).block = st.block := rfl
@[simp] theorem record_time : (st.record c b r).time = st.time := rfl
@[simp] theorem record_chainCount : (st.record c b r).chainCount = st.chainCount := rfl
@[simp] theorem record_chainIndex : (st.record c b r).chainIndex = st.chainIndex := rfl
@[simp] theorem record_chainIndexToId : (st.record c b r).chainIndexToId = st.chainIndexToId := rfl
@[simp] theorem record_current : (st.record c b r).current = Function.update st.current c b := rfl
@[simp] theorem record_batchRoot :
    (st.record c b r).batchRoot = Function.update st.batchRoot c (Function.update (st.batchRoot c) b r) :=
  rfl
@[simp] theorem record_batchTs : (st.record c b r).batchTs = st.batchTs := rfl
@[simp] theorem record_leaves : (st.record c b r).leaves = st.leaves := rfl
@[simp] theorem record_shared : (st.record c b r).shared = st.shared := rfl
@[simp] theorem record_hist : (st.record c b r).hist = st.hist := rfl

@[simp] theorem push_block : (st.push P c b r).block = st.block := rfl
@[simp] theorem push_time : (st.push P c b r).time = st.time := rfl
@[simp] theorem push_chainCount : (st.push P c b r).chainCount = st.chainCount := rfl
@[simp] theorem push_chainIndex : (st.push P c b r).chainIndex = st.chainIndex := rfl
@[simp] theorem push_chainIndexToId : (st.push P c b r).chainIndexToId = st.chainIndexToId := rfl
@[simp] theorem push_current : (st.push P c b r).current = st.current := rfl
@[simp] theorem push_batchRoot : (st.push P c b r).batchRoot = st.batchRoot := rfl
@[simp] theorem push_batchTs :
    (st.push P c b r).batchTs = Function.update st.batchTs c (Function.update (st.batchTs c) b st.time) :=
  rfl
@[simp] theorem push_leaves :
    (st.push P c b r).leaves = Function.update st.leaves c (st.leaves c ++ [st.newLeaf b r]) := rfl
@[simp] theorem push_shared :
    (st.push P c b r).shared = st.shared.set (st.chainIndex c)
      (P.H.chainIdLeaf (chainRootVal P.H (st.leaves c ++ [st.newLeaf b r])) c) := rfl
@[simp] theorem push_hist :
    (st.push P c b r).hist = Function.update st.hist st.block
      (some ⟨P.H.sharedRoot (st.shared.set (st.chainIndex c)
          (P.H.chainIdLeaf (chainRootVal P.H (st.leaves c ++ [st.newLeaf b r])) c)), st.time,
        fun c' => (Function.update st.leaves c (st.leaves c ++ [st.newLeaf b r]) c').length⟩) := rfl

@[simp] theorem newLeaf_batch : (st.newLeaf b r).batch = b := rfl
@[simp] theorem newLeaf_root : (st.newLeaf b r).root = r := rfl
@[simp] theorem newLeaf_ts : (st.newLeaf b r).ts = st.time := rfl
@[simp] theorem newLeaf_blk : (st.newLeaf b r).blk = st.block := rfl

@[simp] theorem migrate_block : (st.migrate c b).block = st.block := rfl
@[simp] theorem migrate_time : (st.migrate c b).time = st.time := rfl
@[simp] theorem migrate_chainCount : (st.migrate c b).chainCount = st.chainCount := rfl
@[simp] theorem migrate_chainIndex : (st.migrate c b).chainIndex = st.chainIndex := rfl
@[simp] theorem migrate_chainIndexToId : (st.migrate c b).chainIndexToId = st.chainIndexToId := rfl
@[simp] theorem migrate_current : (st.migrate c b).current = Function.update st.current c b := rfl
@[simp] theorem migrate_batchRoot : (st.migrate c b).batchRoot = st.batchRoot := rfl
@[simp] theorem migrate_batchTs : (st.migrate c b).batchTs = st.batchTs := rfl
@[simp] theorem migrate_leaves : (st.migrate c b).leaves = st.leaves := rfl
@[simp] theorem migrate_shared : (st.migrate c b).shared = st.shared := rfl
@[simp] theorem migrate_hist : (st.migrate c b).hist = st.hist := rfl

@[simp] theorem advance_block : (st.advance τ).block = st.block + 1 := rfl
@[simp] theorem advance_time : (st.advance τ).time = τ := rfl
@[simp] theorem advance_chainCount : (st.advance τ).chainCount = st.chainCount := rfl
@[simp] theorem advance_chainIndex : (st.advance τ).chainIndex = st.chainIndex := rfl
@[simp] theorem advance_chainIndexToId : (st.advance τ).chainIndexToId = st.chainIndexToId := rfl
@[simp] theorem advance_current : (st.advance τ).current = st.current := rfl
@[simp] theorem advance_batchRoot : (st.advance τ).batchRoot = st.batchRoot := rfl
@[simp] theorem advance_batchTs : (st.advance τ).batchTs = st.batchTs := rfl
@[simp] theorem advance_leaves : (st.advance τ).leaves = st.leaves := rfl
@[simp] theorem advance_shared : (st.advance τ).shared = st.shared := rfl
@[simp] theorem advance_hist : (st.advance τ).hist = st.hist := rfl

end fields

theorem registered_addChain_iff {P : Params} {st : State} {c c' : ChainId} {s : ℕ}
    (hcount : 1 ≤ st.chainCount) :
    (st.addChain P c s).Registered P c' ↔ c' = c ∨ st.Registered P c' := by
  unfold State.Registered
  simp only [addChain_chainIndex]
  by_cases h : c' = c
  · subst h; simp; omega
  · simp [h]

end Contracts.MessageRoot

namespace Contracts.MessageRoot

/-! ## The run invariant -/

/-- What every state reachable from `_initialize` satisfies, under either timestamp rule. -/
structure AggInv (P : Params) (st : State) : Prop where
  count_pos : 1 ≤ st.chainCount
  shared_len : st.shared.length = st.chainCount
  self_index : st.chainIndex P.self = 0
  index_lt : ∀ c, st.Registered P c → st.chainIndex c < st.chainCount
  index_inv : ∀ c, st.Registered P c → st.chainIndexToId (st.chainIndex c) = c
  shared_leaf : ∀ c, st.Registered P c →
    st.shared[st.chainIndex c]? = some (P.H.chainIdLeaf (chainRootVal P.H (st.leaves c)) c)
  unreg_leaves : ∀ c, ¬ st.Registered P c → st.leaves c = []
  unreg_roots : ∀ c b, ¬ st.Registered P c → st.batchRoot c b = 0
  above_current : ∀ c b, st.current c < b → st.batchRoot c b = 0
  sorted : ∀ c, (st.leaves c).Pairwise (fun l l' => l.batch < l'.batch ∧ l.ts ≤ l'.ts ∧ l.blk ≤ l'.blk)
  leaf_recorded : ∀ c, ∀ l ∈ st.leaves c, st.batchRoot c l.batch = l.root ∧ l.root ≠ 0 ∧
    st.batchTs c l.batch = l.ts ∧ l.batch ≤ st.current c
  leaf_past : ∀ c, ∀ l ∈ st.leaves c, l.blk ≤ st.block ∧ l.ts ≤ st.time ∧
    (l.blk = st.block → l.ts = st.time)
  unpushed_ts : ∀ c b, (∀ l ∈ st.leaves c, l.batch ≠ b) → st.batchTs c b = 0
  hist_past : ∀ b e, st.hist b = some e → b ≤ st.block ∧ e.ts ≤ st.time ∧ (b = st.block → e.ts = st.time)
  hist_count : ∀ b e, st.hist b = some e → ∀ c, e.count c ≤ (st.leaves c).length ∧
    ∀ i (hi : i < (st.leaves c).length), (i < e.count c ↔ ((st.leaves c)[i]).blk ≤ b)
  hist_ts : ∀ b e, st.hist b = some e → ∀ c, ∀ l ∈ st.leaves c, l.blk = b → l.ts = e.ts
  hist_later : ∀ b e, st.hist b = some e → ∀ c, ∀ l ∈ st.leaves c, b < l.blk → e.ts ≤ l.ts
  hist_current : ∀ e, st.hist st.block = some e → e.root = P.H.sharedRoot st.shared ∧
    e.ts = st.time ∧ ∀ c, e.count c = (st.leaves c).length

section initFields
variable (P : Params) (b0 τ0 : ℕ)

@[simp] theorem init_block : (init P b0 τ0).block = b0 := rfl
@[simp] theorem init_time : (init P b0 τ0).time = τ0 := rfl
@[simp] theorem init_chainCount : (init P b0 τ0).chainCount = 1 := rfl
@[simp] theorem init_chainIndex : (init P b0 τ0).chainIndex = fun _ => 0 := by
  funext c; by_cases h : c = P.self <;> simp [init, blank, h]
@[simp] theorem init_chainIndexToId :
    (init P b0 τ0).chainIndexToId = Function.update (fun _ => 0) 0 P.self := rfl
@[simp] theorem init_current : (init P b0 τ0).current = fun _ => 0 := by
  funext c; by_cases h : c = P.self <;> simp [init, blank, h]
@[simp] theorem init_batchRoot : (init P b0 τ0).batchRoot = fun _ _ => 0 := rfl
@[simp] theorem init_batchTs : (init P b0 τ0).batchTs = fun _ _ => 0 := rfl
@[simp] theorem init_leaves : (init P b0 τ0).leaves = fun _ => [] := by
  funext c; by_cases h : c = P.self <;> simp [init, blank, h]
@[simp] theorem init_shared : (init P b0 τ0).shared = [P.H.chainIdLeaf 0 P.self] := rfl
@[simp] theorem init_hist :
    (init P b0 τ0).hist = Function.update (fun _ => none) b0
      (some ⟨P.H.sharedRoot [P.H.chainIdLeaf 0 P.self], τ0, fun _ => 0⟩) := by
  have hl : (fun c' => (Function.update (blank b0 τ0).leaves P.self [] c').length) = fun _ => 0 := by
    funext c'; by_cases h : c' = P.self <;> simp [blank, h]
  simp only [init, addChain_hist, hl]
  rfl

end initFields

theorem registered_init_iff {P : Params} {b0 τ0 : ℕ} {c : ChainId} :
    (init P b0 τ0).Registered P c ↔ c = P.self := by
  unfold State.Registered
  simp

theorem init_hist_eq {P : Params} {b0 τ0 b : ℕ} {e : HistEntry}
    (he : (init P b0 τ0).hist b = some e) :
    b = b0 ∧ e = ⟨P.H.sharedRoot [P.H.chainIdLeaf 0 P.self], τ0, fun _ => 0⟩ := by
  simp only [init_hist] at he
  by_cases hb : b = b0
  · subst hb; simp at he; exact ⟨rfl, he.symm⟩
  · simp [Function.update_of_ne hb] at he

theorem aggInv_init (P : Params) (b0 τ0 : ℕ) : AggInv P (init P b0 τ0) where
  count_pos := by simp
  shared_len := by simp
  self_index := by simp
  index_lt := by
    intro c hc
    rw [registered_init_iff] at hc
    simp
  index_inv := by
    intro c hc
    rw [registered_init_iff] at hc
    subst hc; simp
  shared_leaf := by
    intro c hc
    rw [registered_init_iff] at hc
    subst hc; simp [chainRootVal]
  unreg_leaves := by intro c _; simp
  unreg_roots := by intro c b _; simp
  above_current := by intro c b _; simp
  sorted := by intro c; simp
  leaf_recorded := by intro c l hl; simp at hl
  leaf_past := by intro c l hl; simp at hl
  unpushed_ts := by intro c b _; simp
  hist_past := by
    intro b e he
    obtain ⟨rfl, rfl⟩ := init_hist_eq he
    simp
  hist_count := by
    intro b e he c
    obtain ⟨rfl, rfl⟩ := init_hist_eq he
    simp
  hist_ts := by intro b e he c l hl; simp at hl
  hist_later := by intro b e he c l hl; simp at hl
  hist_current := by
    intro e he
    obtain ⟨-, rfl⟩ := init_hist_eq he
    simp

/-! ### Steps that leave the trees alone -/

theorem aggInv_advance {P : Params} {st : State} {τ : ℕ} (hI : AggInv P st) (hτ : st.time ≤ τ) :
    AggInv P (st.advance τ) where
  count_pos := hI.count_pos
  shared_len := hI.shared_len
  self_index := hI.self_index
  index_lt := hI.index_lt
  index_inv := hI.index_inv
  shared_leaf := hI.shared_leaf
  unreg_leaves := hI.unreg_leaves
  unreg_roots := hI.unreg_roots
  above_current := hI.above_current
  sorted := hI.sorted
  leaf_recorded := hI.leaf_recorded
  leaf_past := by
    intro c l hl
    obtain ⟨h1, h2, _⟩ := hI.leaf_past c l hl
    simp only [advance_block, advance_time]
    omega
  unpushed_ts := hI.unpushed_ts
  hist_past := by
    intro b e he
    obtain ⟨h1, h2, _⟩ := hI.hist_past b e he
    simp only [advance_block, advance_time]
    omega
  hist_count := hI.hist_count
  hist_ts := hI.hist_ts
  hist_later := hI.hist_later
  hist_current := by
    intro e he
    simp only [advance_hist, advance_block] at he
    exact absurd (hI.hist_past _ e he).1 (by omega)

theorem aggInv_migrate {P : Params} {st : State} {c : ChainId} {b : ℕ} (hI : AggInv P st)
    (hb : st.current c ≤ b) : AggInv P (st.migrate c b) where
  count_pos := hI.count_pos
  shared_len := hI.shared_len
  self_index := hI.self_index
  index_lt := hI.index_lt
  index_inv := hI.index_inv
  shared_leaf := hI.shared_leaf
  unreg_leaves := hI.unreg_leaves
  unreg_roots := hI.unreg_roots
  above_current := by
    intro c' b' hlt
    simp only [migrate_current, migrate_batchRoot] at hlt ⊢
    by_cases hc : c' = c
    · subst hc; simp at hlt; exact hI.above_current _ _ (by omega)
    · rw [Function.update_of_ne hc] at hlt; exact hI.above_current _ _ hlt
  sorted := hI.sorted
  leaf_recorded := by
    intro c' l hl
    obtain ⟨h1, h2, h3, h4⟩ := hI.leaf_recorded c' l hl
    refine ⟨h1, h2, h3, ?_⟩
    simp only [migrate_current]
    by_cases hc : c' = c
    · subst hc; simp; omega
    · rw [Function.update_of_ne hc]; exact h4
  leaf_past := hI.leaf_past
  unpushed_ts := hI.unpushed_ts
  hist_past := hI.hist_past
  hist_count := hI.hist_count
  hist_ts := hI.hist_ts
  hist_later := hI.hist_later
  hist_current := hI.hist_current

theorem aggInv_record {P : Params} {st : State} {c : ChainId} {b : ℕ} {r : Word}
    (hI : AggInv P st) (hg : RecordGuard P st c b r) : AggInv P (st.record c b r) where
  count_pos := hI.count_pos
  shared_len := hI.shared_len
  self_index := hI.self_index
  index_lt := hI.index_lt
  index_inv := hI.index_inv
  shared_leaf := hI.shared_leaf
  unreg_leaves := hI.unreg_leaves
  unreg_roots := by
    intro c' b' hc'
    have hne : c' ≠ c := fun h => hc' (h ▸ hg.registered)
    simp only [record_batchRoot, Function.update_of_ne hne]
    exact hI.unreg_roots c' b' hc'
  above_current := by
    intro c' b' hlt
    simp only [record_current, record_batchRoot] at hlt ⊢
    by_cases hc : c' = c
    · subst hc
      simp only [Function.update_self] at hlt ⊢
      have hne : b' ≠ b := by omega
      rw [Function.update_of_ne hne]
      exact hI.above_current _ _ (by have := hg.consecutive; omega)
    · rw [Function.update_of_ne hc] at hlt ⊢; exact hI.above_current _ _ hlt
  sorted := hI.sorted
  leaf_recorded := by
    intro c' l hl
    obtain ⟨h1, h2, h3, h4⟩ := hI.leaf_recorded c' l hl
    simp only [record_batchRoot, record_current, record_batchTs]
    by_cases hc : c' = c
    · subst hc
      have hne : l.batch ≠ b := by have := hg.consecutive; omega
      simp only [Function.update_self, Function.update_of_ne hne]
      exact ⟨h1, h2, h3, by have := hg.consecutive; omega⟩
    · simp only [Function.update_of_ne hc]; exact ⟨h1, h2, h3, h4⟩
  leaf_past := hI.leaf_past
  unpushed_ts := hI.unpushed_ts
  hist_past := hI.hist_past
  hist_count := hI.hist_count
  hist_ts := hI.hist_ts
  hist_later := hI.hist_later
  hist_current := hI.hist_current

/-! ### `_pushChainBatchRoot` -/

section push
variable {P : Params} {st : State} {c : ChainId} {b : ℕ} {r : Word}

theorem mem_push_leaves {c' : ChainId} {l : Leaf} :
    l ∈ (st.push P c b r).leaves c' ↔ l ∈ st.leaves c' ∨ (c' = c ∧ l = st.newLeaf b r) := by
  simp only [push_leaves]
  by_cases hcc : c' = c
  · subst hcc; simp
  · simp [hcc]

theorem push_leaf_past (hI : AggInv P st) :
    ∀ c', ∀ l ∈ (st.push P c b r).leaves c', l.blk ≤ st.block ∧ l.ts ≤ st.time ∧
      (l.blk = st.block → l.ts = st.time) := by
  intro c' l hl
  rcases mem_push_leaves.mp hl with hl | ⟨-, rfl⟩
  · exact hI.leaf_past c' l hl
  · simp

theorem push_index_ne (hI : AggInv P st) (hreg : st.Registered P c) {c' : ChainId}
    (hc' : st.Registered P c') (hcc : c' ≠ c) : st.chainIndex c' ≠ st.chainIndex c := by
  intro h
  have h1 := hI.index_inv c' hc'
  rw [h, hI.index_inv c hreg] at h1
  exact hcc h1.symm

theorem aggInv_push (hI : AggInv P st) (hreg : st.Registered P c) (hroot : st.batchRoot c b = r)
    (hr : r ≠ 0) (hcur : b ≤ st.current c) (hlt : ∀ l ∈ st.leaves c, l.batch < b) :
    AggInv P (st.push P c b r) where
  count_pos := hI.count_pos
  shared_len := by simp [hI.shared_len]
  self_index := hI.self_index
  index_lt := hI.index_lt
  index_inv := hI.index_inv
  shared_leaf := by
    intro c' hc'
    simp only [push_shared, push_leaves, push_chainIndex]
    by_cases hcc : c' = c
    · subst hcc
      have hlt' : st.chainIndex c' < st.shared.length := hI.shared_len ▸ hI.index_lt c' hreg
      simp [List.getElem?_set_self hlt']
    · rw [List.getElem?_set_ne (push_index_ne hI hreg hc' hcc).symm, Function.update_of_ne hcc]
      exact hI.shared_leaf c' hc'
  unreg_leaves := by
    intro c' hc'
    have hne : c' ≠ c := fun h => hc' (h ▸ hreg)
    simp only [push_leaves, Function.update_of_ne hne]
    exact hI.unreg_leaves c' hc'
  unreg_roots := hI.unreg_roots
  above_current := hI.above_current
  sorted := by
    intro c'
    simp only [push_leaves]
    by_cases hcc : c' = c
    · subst hcc
      simp only [Function.update_self]
      rw [List.pairwise_append]
      refine ⟨hI.sorted c', List.pairwise_singleton _ _, ?_⟩
      intro l hl l' hl'
      simp only [List.mem_singleton] at hl'
      subst hl'
      obtain ⟨h1, h2, _⟩ := hI.leaf_past c' l hl
      exact ⟨hlt l hl, h2, h1⟩
    · simp only [Function.update_of_ne hcc]; exact hI.sorted c'
  leaf_recorded := by
    intro c' l hl
    simp only [push_batchRoot, push_batchTs, push_current]
    rcases mem_push_leaves.mp hl with hl' | ⟨rfl, rfl⟩
    · obtain ⟨h1, h2, h3, h4⟩ := hI.leaf_recorded c' l hl'
      refine ⟨h1, h2, ?_, h4⟩
      by_cases hcc : c' = c
      · subst hcc
        have hne : l.batch ≠ b := Nat.ne_of_lt (hlt l hl')
        simp only [Function.update_self, Function.update_of_ne hne]
        exact h3
      · simp only [Function.update_of_ne hcc]; exact h3
    · simp [hroot, hr, hcur]
  leaf_past := push_leaf_past hI
  unpushed_ts := by
    intro c' b' hno
    simp only [push_batchTs]
    by_cases hcc : c' = c
    · subst hcc
      have hb' : b' ≠ b := fun h =>
        hno (st.newLeaf b r) (mem_push_leaves.mpr (Or.inr ⟨rfl, rfl⟩)) (by simp [h])
      simp only [Function.update_self, Function.update_of_ne hb']
      exact hI.unpushed_ts c' b' (fun l hl => hno l (mem_push_leaves.mpr (Or.inl hl)))
    · simp only [Function.update_of_ne hcc]
      exact hI.unpushed_ts c' b' (fun l hl => hno l (mem_push_leaves.mpr (Or.inl hl)))
  hist_past := by
    intro b' e he
    simp only [push_hist, push_block, push_time] at he ⊢
    by_cases hb : b' = st.block
    · subst hb; simp only [Function.update_self, Option.some.injEq] at he; subst he; simp
    · rw [Function.update_of_ne hb] at he
      exact hI.hist_past b' e he
  hist_count := by
    intro b' e he c'
    simp only [push_hist] at he
    by_cases hb : b' = st.block
    · subst hb
      simp only [Function.update_self, Option.some.injEq] at he
      subst he
      refine ⟨le_refl _, fun i hi => ?_⟩
      have hmem := List.getElem_mem hi
      have := (push_leaf_past hI c' _ hmem).1
      simp only [push_leaves] at hi ⊢
      exact ⟨fun _ => this, fun _ => hi⟩
    · rw [Function.update_of_ne hb] at he
      obtain ⟨hcnt, hiff⟩ := hI.hist_count b' e he c'
      have hb' : b' < st.block := lt_of_le_of_ne (hI.hist_past b' e he).1 hb
      simp only [push_leaves]
      by_cases hcc : c' = c
      · subst hcc
        simp only [Function.update_self, List.length_append, List.length_singleton]
        refine ⟨by omega, fun i hi => ?_⟩
        by_cases hil : i < (st.leaves c').length
        · rw [List.getElem_append_left hil]; exact hiff i hil
        · have hi_eq : i = (st.leaves c').length := by omega
          subst hi_eq
          rw [List.getElem_append_right (le_refl _)]
          simp only [Nat.sub_self, List.getElem_cons_zero, newLeaf_blk]
          omega
      · simp only [Function.update_of_ne hcc]; exact ⟨hcnt, hiff⟩
  hist_ts := by
    intro b' e he c' l hl hblk
    simp only [push_hist] at he
    by_cases hb : b' = st.block
    · subst hb
      simp only [Function.update_self, Option.some.injEq] at he
      subst he
      exact (push_leaf_past hI c' l hl).2.2 hblk
    · rw [Function.update_of_ne hb] at he
      rcases mem_push_leaves.mp hl with hl | ⟨-, rfl⟩
      · exact hI.hist_ts b' e he c' l hl hblk
      · exact absurd hblk.symm (by simpa using hb)
  hist_later := by
    intro b' e he c' l hl hblk
    simp only [push_hist] at he
    by_cases hb : b' = st.block
    · subst hb
      exact absurd (push_leaf_past hI c' l hl).1 (by omega)
    · rw [Function.update_of_ne hb] at he
      rcases mem_push_leaves.mp hl with hl | ⟨-, rfl⟩
      · exact hI.hist_later b' e he c' l hl hblk
      · simpa using (hI.hist_past b' e he).2.1
  hist_current := by
    intro e he
    simp only [push_hist, push_block, Function.update_self, Option.some.injEq] at he
    subst he
    exact ⟨rfl, rfl, fun _ => rfl⟩

end push

/-! ### `_addNewChain` -/

section addChain
variable {P : Params} {st : State} {c : ChainId} {s : ℕ}

theorem addChain_leaves_eq (hI : AggInv P st) (hc : ¬ st.Registered P c) :
    Function.update st.leaves c [] = st.leaves := by
  funext c'
  by_cases hcc : c' = c
  · subst hcc; simp [hI.unreg_leaves c' hc]
  · simp [hcc]

theorem aggInv_addChain (hI : AggInv P st) (hc : ¬ st.Registered P c) :
    AggInv P (st.addChain P c s) := by
  have hleaves := addChain_leaves_eq hI hc
  have hcself : c ≠ P.self := fun h => hc (Or.inl h)
  have hidx0 : st.chainIndex c = 0 := by
    by_contra h; exact hc (Or.inr h)
  have hreg : ∀ c', (st.addChain P c s).Registered P c' ↔ c' = c ∨ st.Registered P c' :=
    fun c' => registered_addChain_iff hI.count_pos
  have hcount := hI.count_pos
  refine
    { count_pos := by simp
      shared_len := by simp [hI.shared_len]
      self_index := by simp [Function.update_of_ne hcself.symm, hI.self_index]
      index_lt := ?_
      index_inv := ?_
      shared_leaf := ?_
      unreg_leaves := ?_
      unreg_roots := ?_
      above_current := ?_
      sorted := ?_
      leaf_recorded := ?_
      leaf_past := ?_
      unpushed_ts := ?_
      hist_past := ?_
      hist_count := ?_
      hist_ts := ?_
      hist_later := ?_
      hist_current := ?_ }
  · intro c' hc'
    rcases (hreg c').mp hc' with rfl | hc'
    · simp
    · have hne : c' ≠ c := fun h => hc (h ▸ hc')
      simp only [addChain_chainIndex, addChain_chainCount, Function.update_of_ne hne]
      have := hI.index_lt c' hc'; omega
  · intro c' hc'
    rcases (hreg c').mp hc' with rfl | hc'
    · simp
    · have hne : c' ≠ c := fun h => hc (h ▸ hc')
      have hlt := hI.index_lt c' hc'
      simp only [addChain_chainIndexToId, addChain_chainIndex, Function.update_of_ne hne]
      rw [Function.update_of_ne (Nat.ne_of_lt hlt)]
      exact hI.index_inv c' hc'
  · intro c' hc'
    simp only [addChain_shared, addChain_chainIndex, addChain_leaves, hleaves]
    rcases (hreg c').mp hc' with rfl | hc'
    · simp only [Function.update_self]
      rw [List.getElem?_append_right (by rw [hI.shared_len])]
      simp [hI.shared_len, hI.unreg_leaves c' hc, chainRootVal]
    · have hne : c' ≠ c := fun h => hc (h ▸ hc')
      simp only [Function.update_of_ne hne]
      rw [List.getElem?_append_left (by rw [hI.shared_len]; exact hI.index_lt c' hc')]
      exact hI.shared_leaf c' hc'
  · intro c' hc'
    simp only [addChain_leaves, hleaves]
    exact hI.unreg_leaves c' (fun h => hc' ((hreg c').mpr (Or.inr h)))
  · intro c' b hc'
    exact hI.unreg_roots c' b (fun h => hc' ((hreg c').mpr (Or.inr h)))
  · intro c' b hlt
    simp only [addChain_current, addChain_batchRoot] at hlt ⊢
    by_cases hcc : c' = c
    · subst hcc; exact hI.unreg_roots c' b hc
    · rw [Function.update_of_ne hcc] at hlt; exact hI.above_current c' b hlt
  · intro c'; simp only [addChain_leaves, hleaves]; exact hI.sorted c'
  · intro c' l hl
    simp only [addChain_leaves, hleaves] at hl
    simp only [addChain_batchRoot, addChain_batchTs, addChain_current]
    by_cases hcc : c' = c
    · subst hcc; simp [hI.unreg_leaves c' hc] at hl
    · rw [Function.update_of_ne hcc]; exact hI.leaf_recorded c' l hl
  · intro c' l hl
    simp only [addChain_leaves, hleaves] at hl
    exact hI.leaf_past c' l hl
  · intro c' b hno
    simp only [addChain_leaves, hleaves] at hno
    exact hI.unpushed_ts c' b hno
  · intro b e he
    simp only [addChain_hist, addChain_block, addChain_time] at he ⊢
    by_cases hb : b = st.block
    · subst hb; simp only [Function.update_self, Option.some.injEq] at he; subst he; simp
    · rw [Function.update_of_ne hb] at he; exact hI.hist_past b e he
  · intro b e he c'
    simp only [addChain_hist, addChain_leaves, hleaves] at he ⊢
    by_cases hb : b = st.block
    · subst hb
      simp only [Function.update_self, Option.some.injEq] at he
      subst he
      refine ⟨le_refl _, fun i hi => ?_⟩
      have := (hI.leaf_past c' _ (List.getElem_mem hi)).1
      exact ⟨fun _ => this, fun _ => hi⟩
    · rw [Function.update_of_ne hb] at he; exact hI.hist_count b e he c'
  · intro b e he c' l hl hblk
    simp only [addChain_hist, addChain_leaves, hleaves] at he hl
    by_cases hb : b = st.block
    · subst hb
      simp only [Function.update_self, Option.some.injEq] at he
      subst he
      exact (hI.leaf_past c' l hl).2.2 hblk
    · rw [Function.update_of_ne hb] at he; exact hI.hist_ts b e he c' l hl hblk
  · intro b e he c' l hl hblk
    simp only [addChain_hist, addChain_leaves, hleaves] at he hl
    by_cases hb : b = st.block
    · subst hb; exact absurd (hI.leaf_past c' l hl).1 (by omega)
    · rw [Function.update_of_ne hb] at he; exact hI.hist_later b e he c' l hl hblk
  · intro e he
    simp only [addChain_hist, addChain_block, Function.update_self, Option.some.injEq] at he
    subst he
    simp [hleaves]

end addChain

/-! ### Every step, every run -/

theorem aggInv_seedRoot {P : Params} {st : State} {c : ChainId} {g : Word} (hI : AggInv P st)
    (hg : SeedGuard P st c g) : AggInv P (st.setBatchRoot c 0 g) ∧ st.leaves c = [] := by
  have hnil : st.leaves c = [] := by
    rcases hL : st.leaves c with _ | ⟨l, ls⟩
    · rfl
    · have hl : l ∈ st.leaves c := by rw [hL]; exact List.mem_cons_self
      obtain ⟨h1, h2, _, h4⟩ := hI.leaf_recorded c l hl
      have h0 : l.batch = 0 := by have := hg.atGenesis; omega
      rw [h0, hg.unseeded] at h1
      exact absurd h1.symm h2
  refine ⟨{ hI with
    unreg_roots := ?_
    above_current := ?_
    leaf_recorded := ?_ }, hnil⟩
  · intro c' b hc'
    have hne : c' ≠ c := fun h => hc' (h ▸ hg.registered)
    simp only [setBatchRoot_batchRoot, Function.update_of_ne hne]
    exact hI.unreg_roots c' b hc'
  · intro c' b hlt
    simp only [setBatchRoot_batchRoot, setBatchRoot_current] at hlt ⊢
    by_cases hcc : c' = c
    · subst hcc
      have hb : b ≠ 0 := by have := hg.atGenesis; omega
      simp only [Function.update_self, Function.update_of_ne hb]
      exact hI.above_current c' b hlt
    · simp only [Function.update_of_ne hcc]; exact hI.above_current c' b hlt
  · intro c' l hl
    simp only [setBatchRoot_leaves] at hl
    simp only [setBatchRoot_batchRoot, setBatchRoot_batchTs, setBatchRoot_current]
    by_cases hcc : c' = c
    · subst hcc; rw [hnil] at hl; simp at hl
    · simp only [Function.update_of_ne hcc]; exact hI.leaf_recorded c' l hl

theorem aggInv_step {P : Params} {r : TsRule} {st st' : State} (hs : Step P r st st')
    (hI : AggInv P st) : AggInv P st' := by
  cases hs with
  | addNewChain c start hc => exact aggInv_addChain hI hc
  | seedGenesisRoot c g hg =>
    obtain ⟨hI', hnil⟩ := aggInv_seedRoot hI hg
    refine aggInv_push hI' hg.registered (by simp) hg.nonzero (by simp [hg.atGenesis]) ?_
    intro l hl
    simp only [setBatchRoot_leaves, hnil] at hl
    simp at hl
  | addChainBatchRoot c b root hg => exact aggInv_record hI hg
  | addChainBatchRootV32 c b root hg =>
    have hI' := aggInv_record hI hg
    refine aggInv_push hI' hg.registered (by simp) hg.nonzero (by simp) ?_
    intro l hl
    have := (hI.leaf_recorded c l hl).2.2.2
    have := hg.consecutive
    omega
  | setMigratingChainBatchNumber c b hb => exact aggInv_migrate hI hb
  | nextBlock τ hτ =>
    refine aggInv_advance hI ?_
    cases r with
    | mono => exact hτ
    | strict => exact le_of_lt hτ

theorem aggInv_reach {P : Params} {r : TsRule} {st st' : State} (hr : Reach P r st st')
    (hI : AggInv P st) : AggInv P st' := by
  induction hr with
  | refl => exact hI
  | tail _ hs ih => exact aggInv_step hs ih

theorem aggInv_reachable {P : Params} {r : TsRule} {st : State} (hr : Reachable P r st) :
    AggInv P st := by
  obtain ⟨b0, τ0, hr⟩ := hr
  exact aggInv_reach hr (aggInv_init P b0 τ0)

theorem reachable_tail {P : Params} {r : TsRule} {st st' : State} (h1 : Reachable P r st)
    (h2 : Reach P r st st') : Reachable P r st' := by
  obtain ⟨b0, τ0, h1⟩ := h1
  refine ⟨b0, τ0, ?_⟩
  induction h2 with
  | refl => exact h1
  | tail _ hs ih => exact Reach.tail ih hs

/-! ## Strictly increasing timestamps -/

/-- What every state reachable under `StrictTs` also satisfies. -/
structure AggInvStrict (st : State) : Prop where
  hist_before : ∀ b e, st.hist b = some e → b < st.block → e.ts < st.time
  hist_later_strict : ∀ b e, st.hist b = some e → ∀ c, ∀ l ∈ st.leaves c, b < l.blk → e.ts < l.ts

theorem aggInvStrict_init (P : Params) (b0 τ0 : ℕ) : AggInvStrict (init P b0 τ0) where
  hist_before := by
    intro b e he hb
    obtain ⟨rfl, -⟩ := init_hist_eq he
    simp at hb
  hist_later_strict := by intro b e he c l hl; simp at hl

theorem aggInvStrict_push {P : Params} {st : State} {c : ChainId} {b : ℕ} {r : Word}
    (hI : AggInv P st) (hS : AggInvStrict st) : AggInvStrict (st.push P c b r) where
  hist_before := by
    intro b' e he hb
    simp only [push_hist, push_block, push_time] at he hb ⊢
    rw [Function.update_of_ne (Nat.ne_of_lt hb)] at he
    exact hS.hist_before b' e he hb
  hist_later_strict := by
    intro b' e he c' l hl hblk
    simp only [push_hist] at he
    by_cases hb : b' = st.block
    · subst hb; exact absurd (push_leaf_past hI c' l hl).1 (by omega)
    · rw [Function.update_of_ne hb] at he
      rcases mem_push_leaves.mp hl with hl | ⟨-, rfl⟩
      · exact hS.hist_later_strict b' e he c' l hl hblk
      · simpa using hS.hist_before b' e he (lt_of_le_of_ne (hI.hist_past b' e he).1 hb)

theorem aggInvStrict_step {P : Params} {st st' : State} (hs : Step P .strict st st')
    (hI : AggInv P st) (hS : AggInvStrict st) : AggInvStrict st' := by
  cases hs with
  | addNewChain c start hc =>
    have hleaves := addChain_leaves_eq hI hc
    refine ⟨?_, ?_⟩
    · intro b e he hb
      simp only [addChain_hist, addChain_block, addChain_time] at he hb ⊢
      rw [Function.update_of_ne (Nat.ne_of_lt hb)] at he
      exact hS.hist_before b e he hb
    · intro b e he c' l hl hblk
      simp only [addChain_hist, addChain_leaves, hleaves] at he hl
      by_cases hb : b = st.block
      · subst hb; exact absurd (hI.leaf_past c' l hl).1 (by omega)
      · rw [Function.update_of_ne hb] at he; exact hS.hist_later_strict b e he c' l hl hblk
  | seedGenesisRoot c g hg =>
    obtain ⟨hI', -⟩ := aggInv_seedRoot hI hg
    exact aggInvStrict_push hI' ⟨hS.hist_before, hS.hist_later_strict⟩
  | addChainBatchRoot c b root hg => exact ⟨hS.hist_before, hS.hist_later_strict⟩
  | addChainBatchRootV32 c b root hg =>
    exact aggInvStrict_push (aggInv_record hI hg) ⟨hS.hist_before, hS.hist_later_strict⟩
  | setMigratingChainBatchNumber c b hb => exact ⟨hS.hist_before, hS.hist_later_strict⟩
  | nextBlock τ hτ =>
    refine ⟨?_, hS.hist_later_strict⟩
    intro b e he _
    have := (hI.hist_past b e he).2.1
    simp only [advance_time]
    exact lt_of_le_of_lt this hτ

theorem aggInvStrict_reachable {P : Params} {st : State} (hr : Reachable P .strict st) :
    AggInvStrict st := by
  obtain ⟨b0, τ0, hr⟩ := hr
  have key : ∀ st', Reach P .strict (init P b0 τ0) st' → AggInv P st' ∧ AggInvStrict st' := by
    intro st' h
    induction h with
    | refl => exact ⟨aggInv_init P b0 τ0, aggInvStrict_init P b0 τ0⟩
    | tail _ hs ih => exact ⟨aggInv_step hs ih.1, aggInvStrict_step hs ih.1 ih.2⟩
  exact (key st hr).2

/-! ## A snapshot stays a lower bound on what is pushed after it -/

/-- Every leaf of `st` at or past `e`'s count settled no earlier than `e` was written. -/
def Frozen (st : State) (e : HistEntry) : Prop :=
  e.ts ≤ st.time ∧ ∀ c, e.count c ≤ (st.leaves c).length ∧
    ∀ i (hi : i < (st.leaves c).length), e.count c ≤ i → e.ts ≤ ((st.leaves c)[i]).ts

theorem frozen_of_hist {P : Params} {st : State} (hI : AggInv P st) {b : ℕ} {e : HistEntry}
    (he : st.hist b = some e) : Frozen st e := by
  refine ⟨(hI.hist_past b e he).2.1, fun c => ⟨(hI.hist_count b e he c).1, fun i hi hle => ?_⟩⟩
  have hiff := (hI.hist_count b e he c).2 i hi
  have hblk : b < ((st.leaves c)[i]).blk := by
    by_contra hcon
    exact absurd (hiff.mpr (Nat.le_of_not_lt hcon)) (by omega)
  exact hI.hist_later b e he c _ (List.getElem_mem hi) hblk

theorem frozen_step {P : Params} {r : TsRule} {st st' : State} (hs : Step P r st st')
    (hI : AggInv P st) {e : HistEntry} (hF : Frozen st e) : Frozen st' e := by
  have hpush : ∀ {st₀ : State} {c : ChainId} {b : ℕ} {root : Word}, st₀.time = st.time →
      Frozen st₀ e → Frozen (st₀.push P c b root) e := by
    intro st₀ c b root htime hF₀
    refine ⟨by simpa using hF₀.1, fun c' => ?_⟩
    obtain ⟨hcnt, hts⟩ := hF₀.2 c'
    simp only [push_leaves]
    by_cases hcc : c' = c
    · subst hcc
      simp only [Function.update_self, List.length_append, List.length_singleton]
      refine ⟨by omega, fun i hi hle => ?_⟩
      by_cases hil : i < (st₀.leaves c').length
      · rw [List.getElem_append_left hil]; exact hts i hil hle
      · have hi_eq : i = (st₀.leaves c').length := by omega
        subst hi_eq
        rw [List.getElem_append_right (le_refl _)]
        simpa using hF₀.1
    · simp only [Function.update_of_ne hcc]; exact ⟨hcnt, hts⟩
  cases hs with
  | addNewChain c start hc =>
    have hleaves := addChain_leaves_eq hI hc
    refine ⟨by simpa using hF.1, fun c' => ?_⟩
    simp only [addChain_leaves, hleaves]
    exact hF.2 c'
  | seedGenesisRoot c g hg => exact hpush rfl hF
  | addChainBatchRoot c b root hg => exact hF
  | addChainBatchRootV32 c b root hg => exact hpush rfl hF
  | setMigratingChainBatchNumber c b hb => exact hF
  | nextBlock τ hτ =>
    refine ⟨?_, hF.2⟩
    simp only [advance_time]
    cases r with
    | mono => exact le_trans hF.1 hτ
    | strict => exact le_trans hF.1 (le_of_lt hτ)

theorem frozen_reach {P : Params} {r : TsRule} {st₁ st₂ : State} (h1 : Reachable P r st₁)
    (h2 : Reach P r st₁ st₂) {e : HistEntry} (hF : Frozen st₁ e) : Frozen st₂ e := by
  induction h2 with
  | refl => exact hF
  | tail h _ ih =>
    rename_i st' st''
    exact frozen_step (by assumption) (aggInv_reachable (reachable_tail h1 h)) ih

theorem aggregatesStrictAt_of_frozen {st : State} {e : HistEntry} (hF : Frozen st e) :
    AggregatesStrictAt st e := by
  intro c i hlt
  unfold State.leafTime at hlt
  cases hget : (st.leaves c)[i]? with
  | none =>
    rw [hget] at hlt
    simp only at hlt
    exact absurd hF.1 (by omega)
  | some l =>
    rw [hget] at hlt
    simp only at hlt
    obtain ⟨hi, hl⟩ := List.getElem?_eq_some_iff.mp hget
    by_contra hcon
    have := (hF.2 c).2 i hi (Nat.le_of_not_lt hcon)
    rw [hl] at this
    omega

/-! ## The clock is monotone -/

theorem leafTime_mono {P : Params} {st : State} (hI : AggInv P st) (c : ChainId) :
    Monotone (st.leafTime c) := by
  intro i j hij
  unfold State.leafTime
  have hpw := List.pairwise_iff_getElem.mp (hI.sorted c)
  cases hi : (st.leaves c)[i]? with
  | none =>
    have hlen : (st.leaves c).length ≤ i := List.getElem?_eq_none_iff.mp hi
    have hj : (st.leaves c)[j]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    rw [hj]
  | some li =>
    obtain ⟨hil, hli⟩ := List.getElem?_eq_some_iff.mp hi
    cases hj : (st.leaves c)[j]? with
    | none =>
      have := (hI.leaf_past c li (hli ▸ List.getElem_mem hil)).2.1
      simp only
      omega
    | some lj =>
      obtain ⟨hjl, hlj⟩ := List.getElem?_eq_some_iff.mp hj
      simp only
      rcases Nat.lt_or_ge i j with hlt | hge
      · have := (hpw i j hil hjl hlt).2.1
        rw [hli, hlj] at this
        exact this
      · have hij' : i = j := le_antisymm hij hge
        subst hij'
        rw [← hli, ← hlj]

/-! ## Write-once batch roots and record-only batches -/

theorem batchRoot_step_frozen {P : Params} {r : TsRule} {st st' : State} (hs : Step P r st st')
    {c : ChainId} {b : ℕ} (h : st.batchRoot c b ≠ 0) : st'.batchRoot c b = st.batchRoot c b := by
  cases hs with
  | addNewChain c' s _ => rfl
  | seedGenesisRoot c' g hg =>
    simp only [State.seed, push_batchRoot, setBatchRoot_batchRoot]
    by_cases hcc : c = c'
    · subst hcc
      have hb : b ≠ 0 := fun h0 => h (h0 ▸ hg.unseeded)
      simp [Function.update_of_ne hb]
    · simp [Function.update_of_ne hcc]
  | addChainBatchRoot c' b' root hg =>
    simp only [record_batchRoot]
    by_cases hcc : c = c'
    · subst hcc
      have hb : b ≠ b' := fun h0 => h (h0 ▸ hg.fresh)
      simp [Function.update_of_ne hb]
    · simp [Function.update_of_ne hcc]
  | addChainBatchRootV32 c' b' root hg =>
    simp only [push_batchRoot, record_batchRoot]
    by_cases hcc : c = c'
    · subst hcc
      have hb : b ≠ b' := fun h0 => h (h0 ▸ hg.fresh)
      simp [Function.update_of_ne hb]
    · simp [Function.update_of_ne hcc]
  | setMigratingChainBatchNumber c' b' _ => rfl
  | nextBlock τ _ => rfl

theorem batchRoot_reach_frozen {P : Params} {r : TsRule} {st st' : State} (hr : Reach P r st st')
    {c : ChainId} {b : ℕ} (h : st.batchRoot c b ≠ 0) : st'.batchRoot c b = st.batchRoot c b := by
  induction hr with
  | refl => rfl
  | tail _ hs ih =>
    rw [batchRoot_step_frozen hs (by rw [ih]; exact h), ih]

theorem recordOnly_step {P : Params} {r : TsRule} {st st' : State} (hs : Step P r st st')
    (hI : AggInv P st) {c : ChainId} {b : ℕ} (hroot : st.batchRoot c b ≠ 0)
    (hno : ∀ l ∈ st.leaves c, l.batch ≠ b) : ∀ l ∈ st'.leaves c, l.batch ≠ b := by
  have hcur : b ≤ st.current c := by
    by_contra hcon
    exact hroot (hI.above_current c b (Nat.lt_of_not_le hcon))
  cases hs with
  | addNewChain c' s hc =>
    simp only [addChain_leaves, addChain_leaves_eq hI hc]; exact hno
  | seedGenesisRoot c' g hg =>
    intro l hl
    simp only [State.seed] at hl
    rcases mem_push_leaves.mp hl with hl | ⟨rfl, rfl⟩
    · exact hno l hl
    · intro h0
      simp only [newLeaf_batch] at h0
      subst h0
      exact hroot hg.unseeded
  | addChainBatchRoot c' b' root hg => exact hno
  | addChainBatchRootV32 c' b' root hg =>
    intro l hl
    rcases mem_push_leaves.mp hl with hl | ⟨rfl, rfl⟩
    · exact hno l hl
    · simp only [newLeaf_batch]
      have := hg.consecutive
      omega
  | setMigratingChainBatchNumber c' b' _ => exact hno
  | nextBlock τ _ => exact hno

/-! ## The properties -/

theorem ChainIndexInjective : Properties.ChainIndexInjective := by
  intro P r st hr c c' hc hc' heq
  have hI := aggInv_reachable hr
  have h1 := hI.index_inv c hc
  have h2 := hI.index_inv c' hc'
  rw [heq] at h1
  exact h1.symm.trans h2

theorem ChainIndexIsAPosition : Properties.ChainIndexIsAPosition := by
  intro P r st hr
  have hI := aggInv_reachable hr
  exact ⟨hI.shared_len, hI.self_index, fun c hc => ⟨hI.index_lt c hc, hI.index_inv c hc⟩⟩

theorem SharedLeafIsChainIdLeaf : Properties.SharedLeafIsChainIdLeaf :=
  fun _ _ _ hr c hc => (aggInv_reachable hr).shared_leaf c hc

theorem FreshChainLeafIsZeroRoot : Properties.FreshChainLeafIsZeroRoot := by
  intro P r st hr c hc hnil
  rw [(aggInv_reachable hr).shared_leaf c hc, hnil]
  rfl

theorem ChainLeavesArePushedBatches : Properties.ChainLeavesArePushedBatches := by
  intro P r st hr c
  have hI := aggInv_reachable hr
  exact ⟨(hI.sorted c).imp (fun h => h.1), hI.leaf_recorded c⟩

theorem UnrecordedAboveCurrent : Properties.UnrecordedAboveCurrent :=
  fun _ _ _ hr => (aggInv_reachable hr).above_current

theorem BatchRootWriteOnce : Properties.BatchRootWriteOnce :=
  fun _ _ _ _ hr _ _ h => batchRoot_reach_frozen hr h

theorem UnregisteredChainHoldsNothing : Properties.UnregisteredChainHoldsNothing := by
  intro P r st hr c hc
  have hI := aggInv_reachable hr
  exact ⟨hI.unreg_leaves c hc, fun b => hI.unreg_roots c b hc⟩

theorem LeavesOrdered : Properties.LeavesOrdered := by
  intro P r st hr c
  have hI := aggInv_reachable hr
  exact ⟨(hI.sorted c).imp (fun h => ⟨h.2.1, h.2.2⟩),
    fun l hl => ⟨(hI.leaf_past c l hl).2.1, (hI.leaf_past c l hl).1⟩⟩

theorem LeafTimeMonotone : Properties.LeafTimeMonotone :=
  fun _ _ _ hr c => leafTime_mono (aggInv_reachable hr) c

theorem leafTime_le_succ_time {P : Params} {st : State} (hI : AggInv P st) (c : ChainId) (i : ℕ) :
    st.leafTime c i ≤ st.time + 1 := by
  unfold State.leafTime
  cases hget : (st.leaves c)[i]? with
  | none => exact le_refl _
  | some l =>
    obtain ⟨hi, hl⟩ := List.getElem?_eq_some_iff.mp hget
    have := (hI.leaf_past c l (hl ▸ List.getElem_mem hi)).2.1
    simp only
    omega

theorem LeafTimeMonotoneAsWord : Properties.LeafTimeMonotoneAsWord := by
  intro P r st hr hbound c i j hij
  have hI := aggInv_reachable hr
  have hmono := leafTime_mono hI c hij
  have hi := leafTime_le_succ_time hI c i
  have hj := leafTime_le_succ_time hI c j
  show ((st.leafTime c i : ℕ) : UInt256).val ≤ ((st.leafTime c j : ℕ) : UInt256).val
  rw [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  exact hmono

theorem HistoricalRootIsSnapshot : Properties.HistoricalRootIsSnapshot := by
  intro P r st hr b e he
  have hI := aggInv_reachable hr
  obtain ⟨h1, h2, -⟩ := hI.hist_past b e he
  refine ⟨h1, h2, fun c => ⟨(hI.hist_count b e he c).1, fun i hi => ⟨?_, ?_⟩⟩⟩
  · exact (hI.hist_count b e he c).2 i hi
  · exact fun hb => hI.hist_ts b e he c _ (List.getElem_mem hi) hb

theorem LastWriteInBlockWins : Properties.LastWriteInBlockWins :=
  fun _ _ _ hr e he => (aggInv_reachable hr).hist_current e he

theorem aggregatesStrictAt_reach {P : Params} {r : TsRule} {st₁ st₂ : State}
    (h1 : Reachable P r st₁) (h2 : Reach P r st₁ st₂) {b : ℕ} {e : HistEntry}
    (he : st₁.hist b = some e) : AggregatesStrictAt st₂ e :=
  aggregatesStrictAt_of_frozen (frozen_reach h1 h2 (frozen_of_hist (aggInv_reachable h1) he))

theorem AggregatesStrictFromMessageRoot : Properties.AggregatesStrictFromMessageRoot :=
  fun _ _ _ _ h1 h2 _ _ he => aggregatesStrictAt_reach h1 h2 he

theorem aggregatesAt_strict {P : Params} {st : State} (hr : Reachable P .strict st) {b : ℕ}
    {e : HistEntry} (he : st.hist b = some e) : AggregatesAt st e := by
  intro c i hle
  have hI := aggInv_reachable hr
  have hS := aggInvStrict_reachable hr
  unfold State.leafTime at hle
  cases hget : (st.leaves c)[i]? with
  | none =>
    rw [hget] at hle
    simp only at hle
    have := (hI.hist_past b e he).2.1
    omega
  | some l =>
    rw [hget] at hle
    simp only at hle
    obtain ⟨hi, hl⟩ := List.getElem?_eq_some_iff.mp hget
    by_contra hcon
    have hblk : b < ((st.leaves c)[i]).blk := by
      by_contra h'
      exact hcon (((hI.hist_count b e he c).2 i hi).mpr (Nat.le_of_not_lt h'))
    have := hS.hist_later_strict b e he c _ (List.getElem_mem hi) hblk
    rw [hl] at this
    omega

theorem AggregatesFromMessageRootStrictTs : Properties.AggregatesFromMessageRootStrictTs :=
  fun _ _ hr _ _ he => aggregatesAt_strict hr he

theorem PushedAfterLastIsLate : Properties.PushedAfterLastIsLate := by
  intro P r st₁ st₂ h1 h2 b e he c n hn
  by_contra hcon
  exact hn (aggregatesStrictAt_reach h1 h2 he c n (Nat.lt_of_not_le hcon))

theorem RecordOnlyBatchNotCitable : Properties.RecordOnlyBatchNotCitable := by
  intro P r st₁ st₂ h1 h2 c b hroot hno
  have key : ∀ st, Reach P r st₁ st → st.batchRoot c b = st₁.batchRoot c b ∧
      ∀ l ∈ st.leaves c, l.batch ≠ b := by
    intro st h
    induction h with
    | refl => exact ⟨rfl, hno⟩
    | tail h hs ih =>
      have hI := aggInv_reachable (reachable_tail h1 h)
      refine ⟨by rw [batchRoot_step_frozen hs (by rw [ih.1]; exact hroot), ih.1], ?_⟩
      exact recordOnly_step hs hI (by rw [ih.1]; exact hroot) ih.2
  obtain ⟨hr, hl⟩ := key st₂ h2
  exact ⟨hl, (aggInv_reachable (reachable_tail h1 h2)).unpushed_ts c b hl, hr⟩

/-! ## Witness runs

One MessageRoot on chain `0` whose shared root is always `1` and whose other hashes are `0`;
chain `1` is registered at start `0` and seeded with genesis root `7`, or onboarded at start `5`. -/

/-- The witness deployment: chain `0`, shared root `1`, every other hash `0`. -/
def aggWitnessParams : Params := ⟨0, ⟨fun _ _ _ => 0, fun _ _ => 0, fun _ => 0, fun _ => 1⟩⟩

instance (r : TsRule) (a b : ℕ) : Decidable (r.Allows a b) := by
  cases r <;> unfold TsRule.Allows <;> infer_instance

theorem aggWitness_unreg (b0 τ0 : ℕ) :
    ¬ (init aggWitnessParams b0 τ0).Registered aggWitnessParams 1 := by
  rw [registered_init_iff]; decide

theorem aggWitness_reg_one (b0 τ0 s : ℕ) :
    ((init aggWitnessParams b0 τ0).addChain aggWitnessParams 1 s).Registered aggWitnessParams 1 :=
  Or.inr (by simp)

/-- `init`, then chain `1` registered at start `s`. -/
def aggWitnessRegistered (b0 τ0 s : ℕ) : State :=
  (init aggWitnessParams b0 τ0).addChain aggWitnessParams 1 s

theorem aggWitnessRegistered_reach (r : TsRule) (b0 τ0 s : ℕ) :
    Reach aggWitnessParams r (init aggWitnessParams b0 τ0) (aggWitnessRegistered b0 τ0 s) :=
  Reach.tail Reach.refl (Step.addNewChain 1 s (aggWitness_unreg b0 τ0))

/-- ... then chain `1`'s genesis root `7` seeded. -/
def aggWitnessSeeded (b0 τ0 : ℕ) : State := (aggWitnessRegistered b0 τ0 0).seed aggWitnessParams 1 7

theorem aggWitnessSeeded_reach (r : TsRule) (b0 τ0 : ℕ) :
    Reach aggWitnessParams r (init aggWitnessParams b0 τ0) (aggWitnessSeeded b0 τ0) :=
  Reach.tail (aggWitnessRegistered_reach r b0 τ0 0)
    (Step.seedGenesisRoot 1 7 ⟨by decide, aggWitness_reg_one b0 τ0 0, rfl, rfl⟩)

/-- A `addChainBatchRootV32(1, b, root)` step from a state where chain `1` is registered, its
current batch is `b - 1`, and batch `b` is unrecorded. -/
theorem aggWitness_v32 {r : TsRule} {st : State} (b : ℕ) (root : Word)
    (hreg : st.Registered aggWitnessParams 1) (hroot : root ≠ 0) (hfresh : st.batchRoot 1 b = 0)
    (hcur : b = st.current 1 + 1) :
    Step aggWitnessParams r st ((st.record 1 b root).push aggWitnessParams 1 b root) :=
  Step.addChainBatchRootV32 1 b root ⟨hreg, hroot, hfresh, hcur⟩

/-! ### Run A: strict timestamps, three blocks -/

/-- Block 0 at time 1: register and seed chain 1. Block 1 at time 2: push its batch 1. -/
def aggRunA4 : State :=
  (((aggWitnessSeeded 0 1).advance 2).record 1 1 9).push aggWitnessParams 1 1 9

theorem aggRunA4_reach : Reach aggWitnessParams .strict (init aggWitnessParams 0 1) aggRunA4 :=
  Reach.tail (Reach.tail (aggWitnessSeeded_reach .strict 0 1) (Step.nextBlock 2 (by decide)))
    (aggWitness_v32 1 9 (Or.inr (by decide)) (by decide) rfl rfl)

/-- Block 2 at time 3: batch 2 is only recorded (the v31 entry point). -/
def aggRunAGap : State := (aggRunA4.advance 3).record 1 2 11

theorem aggRunAGap_reach : Reach aggWitnessParams .strict (init aggWitnessParams 0 1) aggRunAGap :=
  Reach.tail (Reach.tail aggRunA4_reach (Step.nextBlock 3 (by decide)))
    (Step.addChainBatchRoot 1 2 11 ⟨Or.inr (by decide), by decide, rfl, rfl⟩)

/-- Block 2 at time 3: batch 2 is pushed. -/
def aggRunA6 : State := ((aggRunA4.advance 3).record 1 2 11).push aggWitnessParams 1 2 11

theorem aggRunA6_reach : Reach aggWitnessParams .strict aggRunA4 aggRunA6 :=
  Reach.tail (Reach.tail Reach.refl (Step.nextBlock 3 (by decide)))
    (aggWitness_v32 2 11 (Or.inr (by decide)) (by decide) rfl rfl)

theorem AggregationWitness : Properties.AggregationWitness := by
  refine ⟨aggWitnessParams, aggRunA4, aggRunA6, 1, _, 1, ⟨0, 1, aggRunA4_reach⟩, aggRunA6_reach,
    rfl, Or.inr (by decide), by decide, by decide, by decide, by decide, by decide⟩

theorem RecordOnlyGap : Properties.RecordOnlyGap := by
  refine ⟨aggWitnessParams, aggRunAGap, 1, _, 1, ⟨0, 1, aggRunAGap_reach⟩, rfl, by decide, ?_, ?_⟩
  · intro l hl
    have : aggRunAGap.leaves 1 = [⟨0, 7, 1, 0⟩, ⟨1, 9, 2, 1⟩] := by decide
    rw [this] at hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> decide
  · intro hout
    have hn : ¬ aggRunAGap.BatchInFirst 1 2 2 := by
      rintro ⟨l, hl, hb⟩
      have : (aggRunAGap.leaves 1).take 2 = [⟨0, 7, 1, 0⟩, ⟨1, 9, 2, 1⟩] := by decide
      rw [this] at hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp at hb
    have := hout 2 hn
    revert this
    decide

/-! ### Run B: equal timestamps across blocks -/

/-- Block 0 at time 5: register and seed chain 1. Block 1, again at time 5: push batch 1. -/
def aggRunB : State := (((aggWitnessSeeded 0 5).advance 5).record 1 1 9).push aggWitnessParams 1 1 9

theorem aggRunB_reach : Reach aggWitnessParams .mono (init aggWitnessParams 0 5) aggRunB :=
  Reach.tail (Reach.tail (aggWitnessSeeded_reach .mono 0 5) (Step.nextBlock 5 (le_refl 5)))
    (aggWitness_v32 1 9 (Or.inr (by decide)) (by decide) rfl rfl)

theorem EqualTimestampEscapesRoot : Properties.EqualTimestampEscapesRoot := by
  have hr : Reachable aggWitnessParams .mono aggRunB := ⟨0, 5, aggRunB_reach⟩
  refine ⟨aggWitnessParams, aggRunB, 0, _, hr, rfl,
    aggregatesStrictAt_reach (b := 0) hr Reach.refl rfl, ?_⟩
  intro hagg
  have := hagg 1 1 (by decide)
  revert this
  decide

/-! ### Run C: a mid-block read -/

/-- Block 0 at time 5: register and seed chain 1, then (same block) push batch 1. -/
def aggRunC : State := ((aggWitnessSeeded 0 5).record 1 1 9).push aggWitnessParams 1 1 9

theorem MidBlockReadEscapesRoot : Properties.MidBlockReadEscapesRoot := by
  have h1 : Reachable aggWitnessParams .strict (aggWitnessSeeded 0 5) :=
    ⟨0, 5, aggWitnessSeeded_reach .strict 0 5⟩
  have h2 : Reach aggWitnessParams .strict (aggWitnessSeeded 0 5) aggRunC :=
    Reach.tail Reach.refl (aggWitness_v32 1 9 (Or.inr (by decide)) (by decide) rfl rfl)
  refine ⟨aggWitnessParams, aggWitnessSeeded 0 5, aggRunC, 0, _, h1, h2, rfl, rfl,
    aggregatesStrictAt_reach (b := 0) h1 h2 rfl, ?_⟩
  intro hagg
  have := hagg 1 1 (by decide)
  revert this
  decide

/-! ### Run D: a chain onboarded at start 5 -/

/-- Block 0 at time 1: chain 1 onboarded at start 5, then its batch 6 pushed. -/
def aggRunD : State := ((aggWitnessRegistered 0 1 5).record 1 6 9).push aggWitnessParams 1 6 9

theorem OnboardedChainPositionsAreNotBatchNumbers :
    Properties.OnboardedChainPositionsAreNotBatchNumbers := by
  have hr : Reach aggWitnessParams .strict (init aggWitnessParams 0 1) aggRunD :=
    Reach.tail (aggWitnessRegistered_reach .strict 0 1 5)
      (aggWitness_v32 6 9 (Or.inr (by decide)) (by decide) rfl rfl)
  have hleaves : aggRunD.leaves 1 = [⟨6, 9, 1, 0⟩] := by decide
  refine ⟨aggWitnessParams, aggRunD, 0, _, 1, ⟨6, 9, 1, 0⟩, ⟨0, 1, hr⟩, rfl, by decide,
    by rw [hleaves]; rfl, rfl, ?_⟩
  intro n hn l' hl'
  rw [hleaves] at hl'
  simp only [List.mem_singleton] at hl'
  subst hl'
  simp only at hn ⊢
  omega

end Contracts.MessageRoot
