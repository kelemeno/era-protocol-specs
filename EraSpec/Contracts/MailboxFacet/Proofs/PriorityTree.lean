import EraSpec.Contracts.MailboxFacet.Properties.PriorityTree

/-!
# Proofs: the priority tree is append-only and its processed prefix only grows

Proofs of `EraSpec.Contracts.MailboxFacet.Properties.PriorityTree`. Each call is first reduced to
an equation for the state it returns (`push_eq_some`, `processBatch_eq_some`, `l1Reinit_eq_some`,
`gwReinit_eq_some`); the run-level results are inductions over `TreeRun` and `ConsistentRun`.
-/

namespace Contracts.MailboxFacet

theorem checked_eq_some {n m : ℕ} (h : checked n = some m) : m = n ∧ n < wordLimit := by
  unfold checked at h
  split at h
  · rename_i hlt
    exact ⟨(Option.some.inj h).symm, hlt⟩
  · cases h

theorem checked_of_lt {n : ℕ} (h : n < wordLimit) : checked n = some n := by
  unfold checked; rw [if_pos h]

theorem markRoot_self (roots : UInt256 → Bool) (r : UInt256) : markRoot roots r r = true := by
  unfold markRoot; rw [if_pos rfl]

theorem markRoot_mono {roots : UInt256 → Bool} {x : UInt256} (r : UInt256)
    (h : roots x = true) : markRoot roots r x = true := by
  unfold markRoot; split
  · rfl
  · exact h

theorem markRoot_true {roots : UInt256 → Bool} {r x : UInt256} (h : markRoot roots r x = true) :
    roots x = true ∨ x = r := by
  unfold markRoot at h
  split at h
  · rename_i hx; exact Or.inr hx
  · exact Or.inl h

/-! ## `DynamicIncrementalMerkle` -/

namespace PushTree

theorem walkStep_sides_length (h : NodeHash) (zeros : List UInt256) (w : Walk) (i : ℕ) :
    (walkStep h zeros w i).sides.length = w.sides.length := by
  unfold walkStep
  split
  · dsimp only
    split
    · rfl
    · exact List.length_set
  · rfl

theorem foldl_walkStep_sides_length (h : NodeHash) (zeros : List UInt256) (is : List ℕ)
    (w : Walk) : (is.foldl (walkStep h zeros) w).sides.length = w.sides.length := by
  induction is generalizing w with
  | nil => rfl
  | cons i is ih => rw [List.foldl_cons, ih, walkStep_sides_length]

theorem pushZeros_length (h : NodeHash) (t : PushTree) :
    (pushZeros h t).length = if t.Grows then t.zeros.length + 1 else t.zeros.length := by
  unfold pushZeros
  split
  · rw [List.length_append]; rfl
  · rfl

theorem pushSides_length (t : PushTree) :
    (pushSides t).length = if t.Grows then t.sides.length + 1 else t.sides.length := by
  unfold pushSides
  split
  · rw [List.length_append]; rfl
  · rfl

theorem walk_sides_length (h : NodeHash) (t : PushTree) (leaf : UInt256) :
    (walk h t leaf).sides.length = (pushSides t).length := by
  unfold walk
  rw [foldl_walkStep_sides_length]

theorem zeros_prefix_pushZeros (h : NodeHash) (t : PushTree) : t.zeros <+: pushZeros h t := by
  unfold pushZeros
  split
  · exact List.prefix_append _ _
  · exact List.prefix_refl _

/-- A successful `push`, as an equation for what it returns. -/
theorem push_eq_some {h : NodeHash} {t t' : PushTree} {leaf r : UInt256}
    (hp : push h t leaf = some (t', r)) :
    t.zeros.length ≠ 0 ∧ t.nextLeafIndex + 1 < wordLimit
    ∧ t' = { nextLeafIndex := t.nextLeafIndex + 1
             sides := (walk h t leaf).sides.set ((pushZeros h t).length - 1) (walk h t leaf).hash
             zeros := pushZeros h t }
    ∧ r = (walk h t leaf).hash := by
  unfold push at hp
  split at hp
  · cases hp
  · split at hp
    · cases hp
    · rename_i h0 h1
      have hinj := Option.some.inj hp
      exact ⟨h0, by omega, (congrArg Prod.fst hinj).symm, (congrArg Prod.snd hinj).symm⟩

/-- On a tree whose two arrays have equal length, a successful `push` keeps that shape, returns
the root it stores, and adds one leaf. -/
theorem push_shape {h : NodeHash} {t t' : PushTree} {leaf r : UInt256}
    (hs : t.sides.length = t.zeros.length) (hp : push h t leaf = some (t', r)) :
    t'.sides.length = t'.zeros.length ∧ 0 < t'.zeros.length ∧ t'.root = r := by
  obtain ⟨h0, _, ht, hr⟩ := push_eq_some hp
  subst ht hr
  have hlen : (walk h t leaf).sides.length = (pushZeros h t).length := by
    rw [walk_sides_length, pushSides_length, pushZeros_length, hs]
  have hpos : 0 < (pushZeros h t).length := by
    rw [pushZeros_length]; split <;> omega
  have hk : (pushZeros h t).length - 1 < (walk h t leaf).sides.length := by omega
  refine ⟨?_, hpos, ?_⟩
  · show ((walk h t leaf).sides.set _ _).length = (pushZeros h t).length
    rw [List.length_set, hlen]
  · show (((walk h t leaf).sides.set ((pushZeros h t).length - 1) (walk h t leaf).hash).getD
        (((walk h t leaf).sides.set ((pushZeros h t).length - 1) (walk h t leaf).hash).length - 1)
        0) = (walk h t leaf).hash
    rw [List.length_set, hlen, List.getD_eq_getElem?_getD, List.getElem?_set_self hk]
    rfl

end PushTree

/-! ## One call -/

namespace PTree

theorem push_eq_some {P : TreeParams} {t t' : PTree} {x : UInt256} (hp : t.push P x = some t') :
    ∃ tree r, t.tree.push P.node x = some (tree, r)
      ∧ t' = { t with tree := tree, historicalRoots := markRoot t.historicalRoots r } := by
  unfold push at hp
  split at hp
  · cases hp
  · rename_i tree r heq
    exact ⟨tree, r, heq, (Option.some.inj hp).symm⟩

theorem processBatch_eq_some {P : TreeParams} {t t' : PTree} {info : BatchInfo}
    (hp : t.processBatch P info = some t') :
    (info.itemHashes = [] ∧ t' = t)
    ∨ (info.itemHashes ≠ []
        ∧ ∃ r, P.rootPaths info.leftPath info.rightPath t.unprocessedIndex info.itemHashes = some r
          ∧ t.historicalRoots r = true
          ∧ t' = { t with unprocessedIndex := t.unprocessedIndex + info.itemHashes.length }) := by
  unfold processBatch at hp
  split at hp
  · rename_i h0
    exact Or.inl ⟨List.eq_nil_of_length_eq_zero h0, (Option.some.inj hp).symm⟩
  · rename_i h0
    refine Or.inr ⟨fun hnil => h0 (by rw [hnil]; rfl), ?_⟩
    split at hp
    · cases hp
    · rename_i r hr
      split at hp
      · cases hp
      · rename_i hh
        split at hp
        · cases hp
        · rename_i u hu
          obtain ⟨rfl, _⟩ := checked_eq_some hu
          exact ⟨r, hr, by simpa using hh, (Option.some.inj hp).symm⟩

theorem l1Reinit_eq_some {t t' : PTree} {c : Commitment} (hp : t.l1Reinit c = some t') :
    t.startIndex = c.startIndex ∧ t.unprocessedIndex ≤ c.unprocessedIndex
    ∧ c.nextLeafIndex ≤ t.tree.nextLeafIndex
    ∧ t' = { t with unprocessedIndex := c.unprocessedIndex } := by
  unfold l1Reinit at hp
  split at hp
  · cases hp
  · split at hp
    · cases hp
    · split at hp
      · cases hp
      · rename_i h1 h2 h3
        exact ⟨by omega, by omega, by omega, (Option.some.inj hp).symm⟩

theorem zeroCascade_length (P : TreeParams) (n : ℕ) : (zeroCascade P n).length = n := by
  unfold zeroCascade; exact List.length_iterate _ _ _

theorem initFromCommitment_eq_some {P : TreeParams} {t t' : PTree} {c : Commitment}
    (hp : t.initFromCommitment P c = some t') :
    c.sides.length ≠ 0 ∧ t'.startIndex = c.startIndex ∧ t'.unprocessedIndex = c.unprocessedIndex
    ∧ t'.tree.nextLeafIndex = c.nextLeafIndex ∧ t'.tree.sides = c.sides
    ∧ t'.tree.zeros = zeroCascade P c.sides.length
    ∧ t'.historicalRoots = markRoot t.historicalRoots t'.tree.root := by
  unfold initFromCommitment at hp
  split at hp
  · cases hp
  · rename_i hne
    have ht := Option.some.inj hp
    subst ht
    exact ⟨hne, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem gwReinit_eq_some {P : TreeParams} {t t' : PTree} {c : Commitment}
    (hp : t.gwReinit P c = some t') :
    t.startIndex = c.startIndex ∧ t.unprocessedIndex ≤ c.unprocessedIndex
    ∧ t.tree.nextLeafIndex ≤ c.nextLeafIndex ∧ t.initFromCommitment P c = some t' := by
  unfold gwReinit at hp
  split at hp
  · rename_i hc
    unfold checkGWReinit at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨hc.1.1, hc.1.2, hc.2, hp⟩
  · cases hp

/-! ## `WellFormed` -/

theorem setup_wellFormed (P : TreeParams) (t : PTree) (startIndex : ℕ)
    (hs : t.tree.sides.length = t.tree.zeros.length) : (t.setup P startIndex).WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · show (t.tree.sides ++ [0]).length = (t.tree.zeros ++ [P.zeroLeaf]).length
    rw [List.length_append, List.length_append, hs]; rfl
  · show 0 < (t.tree.zeros ++ [P.zeroLeaf]).length
    rw [List.length_append]; exact Nat.succ_pos _
  · show markRoot t.historicalRoots 0
        ((t.tree.sides ++ [0]).getD ((t.tree.sides ++ [0]).length - 1) 0) = true
    have h0 : (t.tree.sides ++ [(0 : UInt256)]).getD ((t.tree.sides ++ [0]).length - 1) 0 = 0 := by
      rw [List.length_append, List.getD_eq_getElem?_getD]
      show (t.tree.sides ++ [(0 : UInt256)])[t.tree.sides.length + 1 - 1]?.getD 0 = 0
      rw [Nat.add_sub_cancel, List.getElem?_concat_length]
      rfl
    rw [h0]
    exact markRoot_self _ _

theorem initFromCommitment_wellFormed {P : TreeParams} {t t' : PTree} {c : Commitment}
    (hp : t.initFromCommitment P c = some t') : t'.WellFormed := by
  obtain ⟨hne, _, _, _, hs, hz, hh⟩ := initFromCommitment_eq_some hp
  refine ⟨?_, ?_, ?_⟩
  · rw [hs, hz, zeroCascade_length]
  · rw [hz, zeroCascade_length]; omega
  · rw [hh]; exact markRoot_self _ _

theorem apply_wellFormed {P : TreeParams} {t t' : PTree} {l : TreeLabel} (hw : t.WellFormed)
    (ha : t.apply P l = some t') : t'.WellFormed := by
  cases l with
  | push x =>
    obtain ⟨tree, r, hp, rfl⟩ := push_eq_some (show t.push P x = some t' from ha)
    obtain ⟨h1, h2, h3⟩ := PushTree.push_shape hw.sameLength hp
    refine ⟨h1, h2, ?_⟩
    show markRoot t.historicalRoots r tree.root = true
    rw [h3]; exact markRoot_self _ _
  | processBatch info =>
    rcases processBatch_eq_some (show t.processBatch P info = some t' from ha) with
      ⟨_, rfl⟩ | ⟨_, r, _, _, rfl⟩
    · exact hw
    · exact ⟨hw.sameLength, hw.nonempty, hw.rootHistorical⟩
  | l1Reinit c =>
    obtain ⟨_, _, _, rfl⟩ := l1Reinit_eq_some (show t.l1Reinit c = some t' from ha)
    exact ⟨hw.sameLength, hw.nonempty, hw.rootHistorical⟩
  | gwReinit c =>
    exact initFromCommitment_wellFormed
      (gwReinit_eq_some (show t.gwReinit P c = some t' from ha)).2.2.2

end PTree

theorem TreeRun.wellFormed {P : TreeParams} {t t' : PTree} {ls : List TreeLabel}
    (hr : TreeRun P t ls t') (hw : t.WellFormed) : t'.WellFormed := by
  induction hr with
  | nil => exact hw
  | snoc l _ ha ih => exact PTree.apply_wellFormed (ih hw) ha

theorem ConsistentRun.toTreeRun {P : TreeParams} {t t' : PTree} {ls : List TreeLabel}
    (hr : ConsistentRun P t ls t') : TreeRun P t ls t' := by
  induction hr with
  | nil => exact TreeRun.nil _
  | snoc l _ _ ha ih => exact TreeRun.snoc l ih ha

/-! ## What one call moves -/

namespace PTree

/-- One call: the counters and the historical roots after it, per label. -/
theorem apply_facts {P : TreeParams} {t t' : PTree} {l : TreeLabel}
    (ha : t.apply P l = some t') :
    t'.startIndex = t.startIndex
    ∧ t.unprocessedIndex ≤ t'.unprocessedIndex
    ∧ (∀ r, t.historicalRoots r = true → t'.historicalRoots r = true)
    ∧ (match l with
        | .push _ => t'.tree.nextLeafIndex = t.tree.nextLeafIndex + 1
            ∧ t'.unprocessedIndex = t.unprocessedIndex
        | .processBatch info => t'.tree = t.tree
            ∧ (t'.unprocessedIndex = t.unprocessedIndex
                ∨ t'.unprocessedIndex = t.unprocessedIndex + info.itemHashes.length)
        | .l1Reinit c => t'.tree = t.tree ∧ t'.unprocessedIndex = c.unprocessedIndex
            ∧ c.nextLeafIndex ≤ t.tree.nextLeafIndex
        | .gwReinit c => t.tree.nextLeafIndex ≤ t'.tree.nextLeafIndex
            ∧ t'.tree.nextLeafIndex = c.nextLeafIndex
            ∧ t'.unprocessedIndex = c.unprocessedIndex) := by
  cases l with
  | push x =>
    obtain ⟨tree, r, hp, rfl⟩ := push_eq_some (show t.push P x = some t' from ha)
    obtain ⟨_, _, rfl, _⟩ := PushTree.push_eq_some hp
    exact ⟨rfl, Nat.le_refl _, fun _ h => markRoot_mono _ h, rfl, rfl⟩
  | processBatch info =>
    rcases processBatch_eq_some (show t.processBatch P info = some t' from ha) with
      ⟨_, rfl⟩ | ⟨_, r, _, _, rfl⟩
    · exact ⟨rfl, Nat.le_refl _, fun _ h => h, rfl, Or.inl rfl⟩
    · exact ⟨rfl, Nat.le_add_right _ _, fun _ h => h, rfl, Or.inr rfl⟩
  | l1Reinit c =>
    obtain ⟨_, h2, h3, rfl⟩ := l1Reinit_eq_some (show t.l1Reinit c = some t' from ha)
    exact ⟨rfl, h2, fun _ h => h, rfl, rfl, h3⟩
  | gwReinit c =>
    obtain ⟨h1, h2, h3, hi⟩ := gwReinit_eq_some (show t.gwReinit P c = some t' from ha)
    obtain ⟨_, e1, e2, e3, _, _, e6⟩ := initFromCommitment_eq_some hi
    refine ⟨by rw [e1, h1], by rw [e2]; exact h2, fun r h => ?_, by rw [e3]; exact h3, e3, e2⟩
    rw [e6]; exact markRoot_mono _ h

theorem apply_nextLeafIndex_le {P : TreeParams} {t t' : PTree} {l : TreeLabel}
    (ha : t.apply P l = some t') : t.tree.nextLeafIndex ≤ t'.tree.nextLeafIndex := by
  have h := (apply_facts ha).2.2.2
  cases l with
  | push x => exact h.1 ▸ Nat.le_succ _
  | processBatch info => rw [h.1]
  | l1Reinit c => rw [h.1]
  | gwReinit c => exact h.1

/-- One call on a `WellFormed` tree adds at most one historical root: the new root. -/
theorem apply_historical {P : TreeParams} {t t' : PTree} {l : TreeLabel} (hw : t.WellFormed)
    (ha : t.apply P l = some t') (r : UInt256) (hr : t'.historicalRoots r = true) :
    t.historicalRoots r = true ∨ r = t'.tree.root := by
  cases l with
  | push x =>
    obtain ⟨tree, r', hp, rfl⟩ := push_eq_some (show t.push P x = some t' from ha)
    obtain ⟨_, _, h3⟩ := PushTree.push_shape hw.sameLength hp
    rcases markRoot_true hr with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans h3.symm)
  | processBatch info =>
    rcases processBatch_eq_some (show t.processBatch P info = some t' from ha) with
      ⟨_, rfl⟩ | ⟨_, r', _, _, rfl⟩
    · exact Or.inl hr
    · exact Or.inl hr
  | l1Reinit c =>
    obtain ⟨_, _, _, rfl⟩ := l1Reinit_eq_some (show t.l1Reinit c = some t' from ha)
    exact Or.inl hr
  | gwReinit c =>
    obtain ⟨_, _, _, hi⟩ := gwReinit_eq_some (show t.gwReinit P c = some t' from ha)
    obtain ⟨_, _, _, _, _, _, e6⟩ := initFromCommitment_eq_some hi
    rw [e6] at hr
    exact markRoot_true hr

theorem push_appends_one_leaf {P : TreeParams} {t t' : PTree} {hash : UInt256}
    (hw : t.WellFormed) (hp : t.push P hash = some t') :
    t'.tree.nextLeafIndex = t.tree.nextLeafIndex + 1
    ∧ t'.startIndex = t.startIndex ∧ t'.unprocessedIndex = t.unprocessedIndex
    ∧ t.tree.zeros <+: t'.tree.zeros
    ∧ t'.historicalRoots = markRoot t.historicalRoots t'.tree.root := by
  obtain ⟨tree, r, hpt, rfl⟩ := push_eq_some hp
  obtain ⟨_, _, h3⟩ := PushTree.push_shape hw.sameLength hpt
  obtain ⟨_, _, ht, _⟩ := PushTree.push_eq_some hpt
  refine ⟨by rw [ht], rfl, rfl, ?_, ?_⟩
  · show t.tree.zeros <+: tree.zeros
    rw [ht]; exact PushTree.zeros_prefix_pushZeros _ _
  · show markRoot t.historicalRoots r = markRoot t.historicalRoots tree.root
    rw [h3]

end PTree

/-! ## Runs -/

theorem tree_run_monotone {P : TreeParams} {t t' : PTree} {ls : List TreeLabel}
    (hr : TreeRun P t ls t') :
    t'.startIndex = t.startIndex
    ∧ t.tree.nextLeafIndex ≤ t'.tree.nextLeafIndex
    ∧ t.unprocessedIndex ≤ t'.unprocessedIndex
    ∧ ∀ r, t.historicalRoots r = true → t'.historicalRoots r = true := by
  induction hr with
  | nil => exact ⟨rfl, Nat.le_refl _, Nat.le_refl _, fun _ h => h⟩
  | snoc l _ ha ih =>
    obtain ⟨i1, i2, i3, i4⟩ := ih
    obtain ⟨a1, a2, a3, _⟩ := PTree.apply_facts ha
    exact ⟨a1.trans i1, Nat.le_trans i2 (PTree.apply_nextLeafIndex_le ha), Nat.le_trans i3 a2,
      fun r h => a3 r (i4 r h)⟩

theorem leaf_count_is_push_count {P : TreeParams} {t t' : PTree} {ls : List TreeLabel}
    (hr : TreeRun P t ls t') (hno : ∀ c, TreeLabel.gwReinit c ∉ ls) :
    t'.tree.nextLeafIndex
      = t.tree.nextLeafIndex
        + (ls.filter (fun l => match l with | .push _ => true | _ => false)).length := by
  induction hr with
  | nil => rfl
  | @snoc t u v ls l _ ha ih =>
    have hno' : ∀ c, TreeLabel.gwReinit c ∉ ls := fun c hc => hno c (List.mem_append_left _ hc)
    have hl : ∀ c, l ≠ TreeLabel.gwReinit c := fun c hc =>
      hno c (List.mem_append_right _ (by rw [hc]; exact List.mem_singleton_self _))
    have h := (PTree.apply_facts ha).2.2.2
    rw [List.filter_append, List.length_append, ← Nat.add_assoc, ← ih hno']
    cases l with
    | push x => exact h.1
    | processBatch info => rw [h.1]; rfl
    | l1Reinit c => rw [h.1]; rfl
    | gwReinit c => exact absurd rfl (hl c)

theorem historical_roots_were_roots {P : TreeParams} {t t' : PTree} {ls : List TreeLabel}
    (hr : TreeRun P t ls t') (hw : t.WellFormed) (r : UInt256)
    (hroot : t'.historicalRoots r = true) :
    t.historicalRoots r = true
    ∨ ∃ (ls₁ ls₂ : List TreeLabel) (u : PTree),
        ls = ls₁ ++ ls₂ ∧ TreeRun P t ls₁ u ∧ u.tree.root = r := by
  induction hr with
  | nil => exact Or.inl hroot
  | @snoc t u v ls l hrun ha ih =>
    rcases PTree.apply_historical (hrun.wellFormed hw) ha r hroot with h | h
    · rcases ih hw h with h' | ⟨ls₁, ls₂, w, hls, hrun₁, hw'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨ls₁, ls₂ ++ [l], w, by rw [hls, List.append_assoc], hrun₁, hw'⟩
    · exact Or.inr ⟨ls ++ [l], [], v, (List.append_nil _).symm, TreeRun.snoc l hrun ha, h.symm⟩

theorem consistent_run_keeps_size {P : TreeParams} {t t' : PTree} {ls : List TreeLabel}
    (hr : ConsistentRun P t ls t') (h0 : t.unprocessedIndex ≤ t.tree.nextLeafIndex) :
    t'.unprocessedIndex ≤ t'.tree.nextLeafIndex := by
  induction hr with
  | nil => exact h0
  | snoc l _ hc ha ih =>
    have hu := ih h0
    have h := (PTree.apply_facts ha).2.2.2
    cases l with
    | push x => rw [h.1, h.2]; exact Nat.le_succ_of_le hu
    | processBatch info =>
      rw [h.1]
      rcases h.2 with e | e
      · rw [e]; exact hu
      · rw [e]; exact hc
    | l1Reinit c => rw [h.1, h.2.1]; exact Nat.le_trans hc h.2.2
    | gwReinit c => rw [h.2.1, h.2.2]; exact hc

/-! ## Witnesses -/

theorem wFresh_wellFormed : wFresh.WellFormed := ⟨rfl, by decide, by decide +kernel⟩

theorem size_needs_consistent_callers : Properties.SizeNeedsConsistentCallers :=
  ⟨wFresh_wellFormed, rfl, rfl, ⟨_, rfl, rfl, rfl⟩, ⟨_, by decide +kernel, rfl, rfl⟩⟩

theorem tree_run_witness : Properties.TreeRunWitness := by
  have r0 := ConsistentRun.nil wParams wFresh
  have r1 := ConsistentRun.snoc (.push 1) r0 trivial rfl
  have r2 := ConsistentRun.snoc (.push 2) r1 trivial rfl
  have r3 := ConsistentRun.snoc (.push 3) r2 trivial rfl
  have r4 := ConsistentRun.snoc (.processBatch ⟨[], [], [1, 2]⟩) r3
    (show (0 : ℕ) + 2 ≤ 3 by decide) rfl
  have r5 := ConsistentRun.snoc (.l1Reinit ⟨3, 5, 2, []⟩) r4 (show (2 : ℕ) ≤ 3 by decide) rfl
  exact ⟨_, r5, rfl, rfl, by decide +kernel, by decide +kernel, rfl, rfl, by decide +kernel⟩

end Contracts.MailboxFacet

/-! ## Certificates -/

namespace Contracts.MailboxFacet

theorem TreeShapeInvariant : Properties.TreeShapeInvariant :=
  fun P => ⟨fun t n hs => PTree.setup_wellFormed P t n hs,
    fun _ _ _ hp => PTree.initFromCommitment_wellFormed hp,
    fun _ _ _ hr hw => hr.wellFormed hw⟩

theorem PushAppendsOneLeaf : Properties.PushAppendsOneLeaf :=
  fun _ _ _ _ hw hp => PTree.push_appends_one_leaf hw hp

theorem TreeRunMonotone : Properties.TreeRunMonotone := fun _ _ _ _ hr => tree_run_monotone hr

theorem LeafCountIsPushCount : Properties.LeafCountIsPushCount :=
  fun _ _ _ _ hr hno => leaf_count_is_push_count hr hno

theorem HistoricalRootsWereRoots : Properties.HistoricalRootsWereRoots :=
  fun _ _ _ _ hr hw r h => historical_roots_were_roots hr hw r h

theorem ProcessBatchChecksHistoricalRoot : Properties.ProcessBatchChecksHistoricalRoot :=
  fun _ _ _ _ hp => by
    rcases PTree.processBatch_eq_some hp with ⟨h0, ht⟩ | ⟨hne, r, hr, hh, ht⟩
    · exact ⟨fun _ => ht, fun hne => absurd h0 hne⟩
    · exact ⟨fun h0 => absurd h0 hne, fun _ => ⟨r, hr, hh, ht⟩⟩

theorem ConsistentRunKeepsSize : Properties.ConsistentRunKeepsSize :=
  fun _ _ t' _ hr h0 => by
    have h := consistent_run_keeps_size hr h0
    refine ⟨h, ?_⟩
    unfold PTree.getSize
    rw [if_pos h]

theorem SizeNeedsConsistentCallers : Properties.SizeNeedsConsistentCallers :=
  size_needs_consistent_callers

theorem TreeRunWitness : Properties.TreeRunWitness := tree_run_witness

end Contracts.MailboxFacet
