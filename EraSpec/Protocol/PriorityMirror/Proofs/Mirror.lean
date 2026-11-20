import EraSpec.Protocol.PriorityMirror.Properties.Mirror

/-!
# Proofs: the gateway's priority tree mirrors L1's, and a migration out and back loses or
repeats no L1 priority operation

Proofs of `EraSpec.Protocol.PriorityMirror.Properties.Mirror`.

* Library facts: `pushAll` from the setup state keeps the incremental tree's shape
  (`_sides` and `_zeros` of equal nonzero length, `_zeros` the padding cascade), so
  `initFromCommitment` of a commitment taken from such a tree rebuilds exactly that tree.
* `SnapInv` and `DInv` (the bookkeeping of dropped relays) hold in every reachable state; `GInv`
  in every consistent one; `MInv` in every honest one. Each is an induction over `Steps`, one
  case per step.
* Witnesses and the countermodel evaluate concrete runs (`runChecked`) with `decide`.
-/

namespace Protocol.PriorityMirror

open Contracts.PriorityTree.Library

/-! ## Library facts -/

theorem pm_checked_eq_some {n m : ℕ} (h : checked n = some m) : m = n ∧ n < wordLimit := by
  unfold checked at h
  split at h
  · rename_i hlt
    exact ⟨(Option.some.inj h).symm, hlt⟩
  · cases h

theorem pm_checked_of_lt {n : ℕ} (h : n < wordLimit) : checked n = some n := by
  unfold checked; simp [h]

theorem pm_markRoot_true {roots : UInt256 → Bool} {r x : UInt256} :
    markRoot roots r x = true ↔ x = r ∨ roots x = true := by
  unfold markRoot
  split
  · rename_i hx; simp [hx]
  · rename_i hx; simp [hx]

/-- The shape every tree pushed from the setup state has: `_sides` and `_zeros` of equal nonzero
length, and `_zeros` the padding leaf followed by its repeated self-hashes. -/
def Shape (P : TreeParams) (t : PushTree) : Prop :=
  t.sides.length = t.zeros.length ∧ 0 < t.zeros.length
  ∧ t.zeros = PTree.zeroCascade P t.zeros.length

theorem pm_setup_shape (P : TreeParams) : Shape P (setupTree P) :=
  ⟨rfl, Nat.zero_lt_one, rfl⟩

theorem pm_cascade_succ (P : TreeParams) (k : ℕ) (hk : 0 < k) :
    PTree.zeroCascade P (k + 1) =
      PTree.zeroCascade P k ++
        [P.node ((PTree.zeroCascade P k).getD (k - 1) 0) ((PTree.zeroCascade P k).getD (k - 1) 0)] := by
  unfold PTree.zeroCascade
  rw [List.iterate_add]
  congr 1
  rw [List.getD_eq_getElem?_getD, List.getElem?_iterate _ _ _ _ (by omega)]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Option.getD_some]
  show [(fun z => P.node z z)^[j + 1] P.zeroLeaf] = [P.node _ _]
  rw [Function.iterate_succ_apply']

theorem pm_walkStep_sides_length (h : NodeHash) (zeros : List UInt256) (w : PushTree.Walk) (i : ℕ) :
    (PushTree.walkStep h zeros w i).sides.length = w.sides.length := by
  unfold PushTree.walkStep
  split
  · dsimp only
    split
    · rfl
    · exact List.length_set
  · rfl

theorem pm_foldl_walkStep_sides_length (h : NodeHash) (zeros : List UInt256) (is : List ℕ)
    (w : PushTree.Walk) : (is.foldl (PushTree.walkStep h zeros) w).sides.length = w.sides.length := by
  induction is generalizing w with
  | nil => rfl
  | cons i is ih => rw [List.foldl_cons, ih, pm_walkStep_sides_length]

theorem pm_push_eq_some {h : NodeHash} {t t' : PushTree} {leaf r : UInt256}
    (hp : t.push h leaf = some (t', r)) :
    t.zeros.length ≠ 0 ∧ t.nextLeafIndex + 1 < wordLimit
    ∧ t' = { nextLeafIndex := t.nextLeafIndex + 1
             sides := (PushTree.walk h t leaf).sides.set ((PushTree.pushZeros h t).length - 1)
               (PushTree.walk h t leaf).hash
             zeros := PushTree.pushZeros h t }
    ∧ r = (PushTree.walk h t leaf).hash := by
  unfold PushTree.push at hp
  split at hp
  · cases hp
  · split at hp
    · cases hp
    · rename_i h0 h1
      have hinj := Option.some.inj hp
      exact ⟨h0, by omega, (congrArg Prod.fst hinj).symm, (congrArg Prod.snd hinj).symm⟩

/-- A push keeps the shape, returns the root it stores, and adds one leaf. -/
theorem pm_push_shape {P : TreeParams} {t t' : PushTree} {leaf r : UInt256}
    (hs : Shape P t) (hp : t.push P.node leaf = some (t', r)) :
    Shape P t' ∧ t'.root = r ∧ t'.nextLeafIndex = t.nextLeafIndex + 1 := by
  obtain ⟨hlen, hpos, hz⟩ := hs
  obtain ⟨_, _, ht, hr⟩ := pm_push_eq_some hp
  subst ht hr
  have hzl : (PushTree.pushZeros P.node t).length
      = if t.Grows then t.zeros.length + 1 else t.zeros.length := by
    unfold PushTree.pushZeros; split
    · rw [List.length_append]; rfl
    · rfl
  have hsl : (PushTree.walk P.node t leaf).sides.length = (PushTree.pushZeros P.node t).length := by
    unfold PushTree.walk
    rw [pm_foldl_walkStep_sides_length, hzl]
    show (PushTree.pushSides t).length = _
    unfold PushTree.pushSides; split
    · rw [List.length_append, hlen]; rfl
    · exact hlen
  have hposz : 0 < (PushTree.pushZeros P.node t).length := by
    rw [hzl]; split <;> omega
  refine ⟨⟨?_, hposz, ?_⟩, ?_, rfl⟩
  · show ((PushTree.walk P.node t leaf).sides.set _ _).length = (PushTree.pushZeros P.node t).length
    rw [List.length_set, hsl]
  · show PushTree.pushZeros P.node t = PTree.zeroCascade P (PushTree.pushZeros P.node t).length
    unfold PushTree.pushZeros
    split
    · rw [List.length_append, List.length_singleton, pm_cascade_succ P _ hpos, ← hz]
    · exact hz
  · have hk : (PushTree.pushZeros P.node t).length - 1 < (PushTree.walk P.node t leaf).sides.length := by
      omega
    show (((PushTree.walk P.node t leaf).sides.set ((PushTree.pushZeros P.node t).length - 1)
        (PushTree.walk P.node t leaf).hash).getD
        (((PushTree.walk P.node t leaf).sides.set ((PushTree.pushZeros P.node t).length - 1)
          (PushTree.walk P.node t leaf).hash).length - 1) 0) = (PushTree.walk P.node t leaf).hash
    rw [List.length_set, hsl, List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega)]
    rfl

theorem pm_pushAll_append (h : NodeHash) (t : PushTree) (L M : List UInt256) :
    pushAll h t (L ++ M) = (pushAll h t L).bind (fun t' => pushAll h t' M) := by
  induction L generalizing t with
  | nil => rfl
  | cons x xs ih =>
    rw [List.cons_append, pushAll.eq_2, pushAll.eq_2]
    cases t.push h x with
    | none => rfl
    | some p =>
      obtain ⟨t', r⟩ := p
      exact ih t'

theorem pm_pushAll_snoc {h : NodeHash} {t t₁ t₂ : PushTree} {L : List UInt256} {x r : UInt256}
    (h1 : pushAll h t L = some t₁) (h2 : t₁.push h x = some (t₂, r)) :
    pushAll h t (L ++ [x]) = some t₂ := by
  rw [pm_pushAll_append, h1]
  show pushAll h t₁ [x] = some t₂
  unfold pushAll
  rw [h2]
  rfl

theorem pm_pushAll_snoc_inv {h : NodeHash} {t t₂ : PushTree} {L : List UInt256} {x : UInt256}
    (hp : pushAll h t (L ++ [x]) = some t₂) :
    ∃ t₁ r, pushAll h t L = some t₁ ∧ t₁.push h x = some (t₂, r) := by
  rw [pm_pushAll_append] at hp
  cases h1 : pushAll h t L with
  | none => rw [h1] at hp; cases hp
  | some t₁ =>
    rw [h1] at hp
    change pushAll h t₁ [x] = some t₂ at hp
    unfold pushAll at hp
    cases h2 : t₁.push h x with
    | none => rw [h2] at hp; cases hp
    | some p =>
      rw [h2] at hp
      obtain ⟨t', r⟩ := p
      exact ⟨t₁, r, rfl, by rw [h2]; exact congrArg (fun u => some (u, r)) (Option.some.inj hp)⟩

theorem pm_pushAll_of_prefix {h : NodeHash} {t t' : PushTree} {L M : List UInt256}
    (hp : pushAll h t L = some t') (hM : M <+: L) : ∃ t'', pushAll h t M = some t'' := by
  obtain ⟨N, rfl⟩ := hM
  rw [pm_pushAll_append] at hp
  cases h1 : pushAll h t M with
  | none => rw [h1] at hp; cases hp
  | some t'' => exact ⟨t'', rfl⟩

/-- Pushing from a shaped tree keeps the shape and adds one leaf per push. -/
theorem pm_pushAll_shape {P : TreeParams} {t t' : PushTree} {L : List UInt256}
    (hs : Shape P t) (hp : pushAll P.node t L = some t') :
    Shape P t' ∧ t'.nextLeafIndex = t.nextLeafIndex + L.length := by
  induction L generalizing t with
  | nil =>
    cases hp
    exact ⟨hs, rfl⟩
  | cons x xs ih =>
    unfold pushAll at hp
    cases h1 : t.push P.node x with
    | none => rw [h1] at hp; cases hp
    | some p =>
      rw [h1] at hp
      obtain ⟨t₁, r⟩ := p
      obtain ⟨hs₁, _, hn₁⟩ := pm_push_shape hs h1
      obtain ⟨hs', hn'⟩ := ih hs₁ hp
      refine ⟨hs', ?_⟩
      rw [hn', hn₁, List.length_cons]
      omega

theorem pm_pushAll_setup {P : TreeParams} {t : PushTree} {L : List UInt256}
    (hp : pushAll P.node (setupTree P) L = some t) :
    Shape P t ∧ t.nextLeafIndex = L.length := by
  obtain ⟨hs, hn⟩ := pm_pushAll_shape (pm_setup_shape P) hp
  exact ⟨hs, by rw [hn]; exact Nat.zero_add _⟩

theorem pm_rootAfter_of_pushAll {P : TreeParams} {t : PushTree} {L : List UInt256}
    (hp : pushAll P.node (setupTree P) L = some t) : rootAfter P L = some t.root := by
  unfold rootAfter; rw [hp]; rfl

/-- `initFromCommitment` of the commitment of a shaped tree rebuilds that tree. -/
theorem pm_rebuild {P : TreeParams} {t : PushTree} (hs : Shape P t) :
    ({ nextLeafIndex := t.nextLeafIndex, sides := t.sides,
       zeros := PTree.zeroCascade P t.sides.length } : PushTree) = t := by
  obtain ⟨hlen, _, hz⟩ := hs
  rw [hlen, ← hz]

/-! ## `PriorityTree` calls -/

theorem pm_ptree_push {P : TreeParams} {t t' : PTree} {x : UInt256} (hp : t.push P x = some t') :
    ∃ tree r, t.tree.push P.node x = some (tree, r)
      ∧ t' = { t with tree := tree, historicalRoots := markRoot t.historicalRoots r } := by
  unfold PTree.push at hp
  split at hp
  · cases hp
  · rename_i tree r heq
    exact ⟨tree, r, heq, (Option.some.inj hp).symm⟩

theorem pm_mailboxWrite {P : TreeParams} {t t' : PTree} {x : UInt256}
    (hw : mailboxWrite P t x = some t') :
    ∃ tree r, t.tree.push P.node x = some (tree, r)
      ∧ t' = { t with tree := tree, historicalRoots := markRoot t.historicalRoots r }
      ∧ t.startIndex + tree.nextLeafIndex < wordLimit := by
  unfold mailboxWrite at hw
  cases hp : t.push P x with
  | none => rw [hp] at hw; cases hw
  | some t₁ =>
    rw [hp] at hw
    dsimp only at hw
    obtain ⟨tree, r, h1, rfl⟩ := pm_ptree_push hp
    cases ht : PTree.getTotalPriorityTxs { t with tree := tree, historicalRoots := markRoot t.historicalRoots r } with
    | none => rw [ht] at hw; cases hw
    | some n =>
      rw [ht] at hw
      refine ⟨tree, r, h1, (Option.some.inj hw).symm, ?_⟩
      exact (pm_checked_eq_some ht).2

theorem pm_mailboxWrite_of_push {P : TreeParams} {t : PTree} {x : UInt256} {tree : PushTree}
    {r : UInt256} (hp : t.tree.push P.node x = some (tree, r))
    (hb : t.startIndex + tree.nextLeafIndex < wordLimit) :
    mailboxWrite P t x = some { t with tree := tree, historicalRoots := markRoot t.historicalRoots r } := by
  unfold mailboxWrite PTree.push
  rw [hp]
  show (match PTree.getTotalPriorityTxs { t with tree := tree, historicalRoots := markRoot t.historicalRoots r } with
    | none => none | some _ => some _) = _
  unfold PTree.getTotalPriorityTxs
  rw [pm_checked_of_lt hb]

theorem pm_processBatch {P : TreeParams} {t t' : PTree} {info : BatchInfo}
    (hp : t.processBatch P info = some t') :
    t' = { t with unprocessedIndex := t.unprocessedIndex + info.itemHashes.length } := by
  unfold PTree.processBatch at hp
  split at hp
  · rename_i h0
    rw [h0, Nat.add_zero]
    exact (Option.some.inj hp).symm
  · split at hp
    · cases hp
    · split at hp
      · cases hp
      · split at hp
        · cases hp
        · rename_i u hu
          rw [(pm_checked_eq_some hu).1] at hp
          exact (Option.some.inj hp).symm

theorem pm_l1Reinit {t t' : PTree} {c : Commitment} (h : t.l1Reinit c = some t') :
    t.startIndex = c.startIndex ∧ t.unprocessedIndex ≤ c.unprocessedIndex
    ∧ c.nextLeafIndex ≤ t.tree.nextLeafIndex
    ∧ t' = { t with unprocessedIndex := c.unprocessedIndex } := by
  unfold PTree.l1Reinit at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i h1 h2 h3
        exact ⟨by simpa using h1, by omega, by omega, (Option.some.inj h).symm⟩

theorem pm_l1Reinit_isSome {t : PTree} {c : Commitment} (h1 : t.startIndex = c.startIndex)
    (h2 : t.unprocessedIndex ≤ c.unprocessedIndex) (h3 : c.nextLeafIndex ≤ t.tree.nextLeafIndex) :
    (t.l1Reinit c).isSome = true := by
  unfold PTree.l1Reinit
  split
  · rename_i h; exact absurd h1 h
  · split
    · omega
    · split
      · omega
      · rfl

theorem pm_initFromCommitment {P : TreeParams} {t t' : PTree} {c : Commitment}
    (h : t.initFromCommitment P c = some t') :
    t'.startIndex = c.startIndex ∧ t'.unprocessedIndex = c.unprocessedIndex
    ∧ t'.tree = { nextLeafIndex := c.nextLeafIndex, sides := c.sides,
                  zeros := PTree.zeroCascade P c.sides.length } := by
  unfold PTree.initFromCommitment at h
  split at h
  · cases h
  · cases h
    exact ⟨rfl, rfl, rfl⟩

theorem pm_getSize_zero {t : PTree} (h : t.getSize = some 0) :
    t.unprocessedIndex = t.tree.nextLeafIndex := by
  unfold PTree.getSize at h
  split at h
  · rename_i hle
    have := Option.some.inj h
    omega
  · cases h

/-! ## One step, as an equation for the state it returns -/

theorem pm_stepRequest {P : Params} {s s' : St} {h : UInt256} (hs : stepRequest P s h = some s') :
    s.d1.frozen = false ∧ depositsPausedL1 P s = false
    ∧ ∃ t, mailboxWrite P.tree s.d1.tree h = some t
      ∧ s' = { s with d1 := { s.d1 with tree := t }, log1 := s.log1 ++ [h],
                      relays := if s.d1.settling then s.relays else s.relays ++ [h] } := by
  unfold stepRequest at hs
  split at hs
  · rename_i hg
    split at hs
    · cases hs
    · rename_i t ht
      exact ⟨hg.1, hg.2, t, ht, (Option.some.inj hs).symm⟩
  · cases hs

theorem pm_stepL1Pipeline {P : Params} {s s' : St} {info : BatchInfo} {b : Batches}
    (hs : stepL1Pipeline P s info b = some s') :
    s.d1.settling = true ∧ s.d1.frozen = false
    ∧ ∃ t, s.d1.tree.processBatch P.tree info = some t
      ∧ s' = { s with d1 := { s.d1 with tree := t, batches := b },
                      executed := s.executed ++
                        slice s.log1 s.d1.tree.unprocessedIndex info.itemHashes.length } := by
  unfold stepL1Pipeline at hs
  split at hs
  · rename_i hg
    split at hs
    · cases hs
    · rename_i t ht
      exact ⟨hg.1, hg.2, t, ht, (Option.some.inj hs).symm⟩
  · cases hs

theorem pm_stepPauseL1 {P : Params} {s s' : St} (hs : stepPauseL1 P s = some s') :
    s.d1.pausedTs = 0 ∧ ∃ ts, s' = { s with d1 := { s.d1 with pausedTs := ts } } := by
  unfold stepPauseL1 at hs
  split at hs
  · rename_i h0
    refine ⟨h0, ?_⟩
    split at hs
    · cases hs
    · split at hs
      · cases hs
      · split at hs
        · split at hs
          · exact ⟨_, (Option.some.inj hs).symm⟩
          · cases hs
        · exact ⟨_, (Option.some.inj hs).symm⟩
  · cases hs

theorem pm_stepUnpauseL1 {s s' : St} (hs : stepUnpauseL1 s = some s') :
    s.d1.pausedTs ≠ 0 ∧ s.inProgress = false ∧ s' = { s with d1 := { s.d1 with pausedTs := 0 } } := by
  unfold stepUnpauseL1 at hs
  split at hs
  · rename_i hg
    exact ⟨hg.1, hg.2, (Option.some.inj hs).symm⟩
  · cases hs

theorem pm_stepFreezeL1 {s s' : St} (hs : stepFreezeL1 s = some s') :
    s' = { s with d1 := { s.d1 with frozen := true } } := by
  unfold stepFreezeL1 at hs
  split at hs
  · exact (Option.some.inj hs).symm
  · cases hs

theorem pm_stepUnfreezeL1 {s s' : St} (hs : stepUnfreezeL1 s = some s') :
    s' = { s with d1 := { s.d1 with frozen := false } } := by
  unfold stepUnfreezeL1 at hs
  split at hs
  · exact (Option.some.inj hs).symm
  · cases hs

theorem pm_stepL1Burn {P : Params} {s s' : St} (hs : stepL1Burn P s = some s') :
    s.phase = .onL1 ∧ P.migrationsEnabled = true ∧ s.d1.settling = true
    ∧ s.d1.tree.getSize = some 0
    ∧ inPausedWindow P.migrationWindow s.d1.pausedTs s.now = true
    ∧ ∃ c, prepare s.d1 = some c
      ∧ s' = { s with d1 := { s.d1 with settling := false }, inProgress := true,
                      phase := .toGW s.d1 c } := by
  unfold stepL1Burn at hs
  split at hs
  · rename_i hp
    split at hs
    · rename_i hg
      split at hs
      · cases hs
      · rename_i c hc
        exact ⟨hp, hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, c, hc, (Option.some.inj hs).symm⟩
    · cases hs
  · cases hs

theorem pm_stepGwMint {P : Params} {s s' : St} (hs : stepGwMint P s = some s') :
    ∃ pre c t b, s.phase = .toGW pre c ∧ P.migrationsEnabled = true ∧ s.d2.isNone = true
      ∧ (emptyTree.setup P.tree 0).initFromCommitment P.tree c.priorityTree = some t
      ∧ mintBatches Batches.zero c = some b
      ∧ s' = { s with
          d2 := some { tree := t, settling := true, pausedTs := 0, frozen := false, batches := b }
          leaves2 := s.log1
          phase := .gwMinted pre } := by
  unfold stepGwMint at hs
  split at hs
  · rename_i pre c hp
    split at hs
    · rename_i hg
      split at hs
      · rename_i t b ht hb
        exact ⟨pre, c, t, b, hp, hg.1, hg.2, ht, hb, (Option.some.inj hs).symm⟩
      · cases hs
    · cases hs
  · cases hs

theorem pm_stepGwMintFails {s s' : St} (hs : stepGwMintFails s = some s') :
    ∃ pre c, s.phase = .toGW pre c ∧ s' = { s with phase := .gwFailed pre } := by
  unfold stepGwMintFails at hs
  split at hs
  · rename_i pre c hp
    exact ⟨pre, c, hp, (Option.some.inj hs).symm⟩
  · cases hs

theorem pm_stepConfirm {s s' : St} {success : Bool} (hs : stepConfirm s success = some s') :
    (∃ pre, s.phase = .gwMinted pre ∧ success = true
        ∧ s' = { s with inProgress := false, d1 := { s.d1 with pausedTs := 0 }, phase := .onGW })
    ∨ (∃ pre, s.phase = .gwFailed pre ∧ success = false ∧ s.d1.settling = false
        ∧ s' = { s with inProgress := false, d1 := { s.d1 with pausedTs := 0, settling := true },
                        phase := .onL1 }) := by
  unfold stepConfirm at hs
  split at hs
  · rename_i _ pre hp
    exact Or.inl ⟨pre, hp, rfl, (Option.some.inj hs).symm⟩
  · rename_i _ pre hp
    split at hs
    · rename_i hg
      exact Or.inr ⟨pre, hp, rfl, hg, (Option.some.inj hs).symm⟩
    · cases hs
  · cases hs

theorem pm_stepRelay {P : Params} {s s' : St} (hs : stepRelay P s = some s') :
    ∃ h rest, s.relays = h :: rest ∧
      ((s' = { s with relays := rest, dropped := s.dropped ++ [h] }
          ∧ (s.d2 = none ∨ ∃ d, s.d2 = some d
              ∧ (d.frozen = true ∨ (d.frozen = false ∧ mailboxWrite P.tree d.tree h = none))))
       ∨ ∃ d t, s.d2 = some d ∧ d.frozen = false ∧ mailboxWrite P.tree d.tree h = some t
          ∧ s' = { s with relays := rest, d2 := some { d with tree := t },
                          leaves2 := s.leaves2 ++ [h] }) := by
  unfold stepRelay at hs
  split at hs
  · cases hs
  · rename_i h rest hr
    refine ⟨h, rest, hr, ?_⟩
    split at hs
    · rename_i hd
      exact Or.inl ⟨(Option.some.inj hs).symm, Or.inl hd⟩
    · rename_i d hd
      split at hs
      · rename_i hf
        exact Or.inl ⟨(Option.some.inj hs).symm, Or.inr ⟨d, hd, Or.inl hf⟩⟩
      · rename_i hf
        split at hs
        · rename_i hw
          exact Or.inl ⟨(Option.some.inj hs).symm, Or.inr ⟨d, hd, Or.inr ⟨by simpa using hf, hw⟩⟩⟩
        · rename_i t hw
          exact Or.inr ⟨d, t, hd, by simpa using hf, hw, (Option.some.inj hs).symm⟩

theorem pm_stepGwPipeline {P : Params} {s s' : St} {info : BatchInfo} {b : Batches}
    (hs : stepGwPipeline P s info b = some s') :
    ∃ d t, s.d2 = some d ∧ d.settling = true ∧ d.frozen = false
      ∧ d.tree.processBatch P.tree info = some t
      ∧ s' = { s with d2 := some { d with tree := t, batches := b },
                      executed := s.executed ++
                        slice s.leaves2 d.tree.unprocessedIndex info.itemHashes.length } := by
  unfold stepGwPipeline at hs
  split at hs
  · cases hs
  · rename_i d hd
    split at hs
    · rename_i hg
      split at hs
      · cases hs
      · rename_i t ht
        exact ⟨d, t, hd, hg.1, hg.2, ht, (Option.some.inj hs).symm⟩
    · cases hs

theorem pm_stepGwPause {s s' : St} {ts : ℕ} (hs : stepGwPause s ts = some s') :
    ∃ d, s.d2 = some d ∧ s' = { s with d2 := some { d with pausedTs := ts } } := by
  unfold stepGwPause at hs
  split at hs
  · cases hs
  · rename_i d hd
    exact ⟨d, hd, (Option.some.inj hs).symm⟩

theorem pm_stepFreezeGW {s s' : St} (hs : stepFreezeGW s = some s') :
    ∃ d, s.d2 = some d ∧ s' = { s with d2 := some { d with frozen := true } } := by
  unfold stepFreezeGW at hs
  split at hs
  · cases hs
  · rename_i d hd
    split at hs
    · exact ⟨d, hd, (Option.some.inj hs).symm⟩
    · cases hs

theorem pm_stepUnfreezeGW {s s' : St} (hs : stepUnfreezeGW s = some s') :
    ∃ d, s.d2 = some d ∧ s' = { s with d2 := some { d with frozen := false } } := by
  unfold stepUnfreezeGW at hs
  split at hs
  · cases hs
  · rename_i d hd
    split at hs
    · exact ⟨d, hd, (Option.some.inj hs).symm⟩
    · cases hs

theorem pm_stepGwBurn {P : Params} {s s' : St} (hs : stepGwBurn P s = some s') :
    ∃ d c, s.phase = .onGW ∧ s.d2 = some d ∧ P.migrationsEnabled = true ∧ d.settling = true
      ∧ d.tree.getSize = some 0 ∧ prepare d = some c
      ∧ s' = { s with d2 := some { d with settling := false }, phase := .toL1 c } := by
  unfold stepGwBurn at hs
  split at hs
  · rename_i d hp hd
    split at hs
    · rename_i hg
      split at hs
      · cases hs
      · rename_i c hc
        exact ⟨d, c, hp, hd, hg.1, hg.2.1, hg.2.2.1, hc, (Option.some.inj hs).symm⟩
    · cases hs
  · cases hs

theorem pm_stepL1Mint {P : Params} {s s' : St} (hs : stepL1Mint P s = some s') :
    ∃ c b t, s.phase = .toL1 c ∧ P.migrationsEnabled = true ∧ s.d1.pausedTs ≠ 0
      ∧ c.priorityTree.sides ≠ []
      ∧ s.d1.tree.isHistoricalRoot (lastSide c.priorityTree) = true ∧ s.d1.settling = false
      ∧ mintBatches s.d1.batches c = some b ∧ s.d1.tree.l1Reinit c.priorityTree = some t
      ∧ s' = { s with d1 := { s.d1 with tree := t, batches := b, settling := true, pausedTs := 0 },
                      phase := .back } := by
  unfold stepL1Mint at hs
  split at hs
  · rename_i c hp
    split at hs
    · rename_i hg
      split at hs
      · rename_i b t hb ht
        exact ⟨c, b, t, hp, hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2, hb, ht,
          (Option.some.inj hs).symm⟩
      · cases hs
    · cases hs
  · cases hs

/-! ## Runs -/

theorem pm_steps_trans {P : Params} {ok : St → Op → Prop} {s t u : St}
    (h1 : Steps P ok s t) (h2 : Steps P ok t u) : Steps P ok s u := by
  induction h2 with
  | refl => exact h1
  | tail op _ hok hst ih => exact Steps.tail op ih hok hst

theorem pm_steps_head {P : Params} {ok : St → Op → Prop} {s t u : St} {op : Op}
    (hok : ok s op) (hst : step P s op = some t) (h : Steps P ok t u) : Steps P ok s u :=
  pm_steps_trans (Steps.tail op (Steps.refl s) hok hst) h

theorem pm_steps_mono {P : Params} {ok ok' : St → Op → Prop} (hmono : ∀ s op, ok s op → ok' s op)
    {s t : St} (h : Steps P ok s t) : Steps P ok' s t := by
  induction h with
  | refl => exact Steps.refl _
  | tail op _ hok hst ih => exact Steps.tail op ih (hmono _ _ hok) hst

/-- An invariant of `step` (under `ok`) holds along every run from a state where it holds. -/
theorem pm_steps_induct {P : Params} {ok : St → Op → Prop} {I : St → Prop}
    (hstep : ∀ s s' op, I s → ok s op → step P s op = some s' → I s')
    {s t : St} (h : Steps P ok s t) (hs : I s) : I t := by
  induction h with
  | refl => exact hs
  | tail op _ hok hst ih => exact hstep _ _ op ih hok hst

/-! ## The phase invariant of every reachable state -/

/-- Between the L1 burn and its confirmation, with `pre` the L1 diamond just before the burn. -/
def Flight (s : St) (pre : ChainDiamond) : Prop :=
  s.inProgress = true ∧ s.d1.settling = false ∧ pre.settling = true ∧ s.d1.tree = pre.tree
  ∧ s.d1.batches = pre.batches ∧ s.d1.pausedTs = pre.pausedTs ∧ pre.pausedTs ≠ 0
  ∧ s.relays = []

/-- What every reachable state satisfies, by phase. -/
def SnapInv (s : St) : Prop :=
  match s.phase with
  | .onL1 => s.d1.settling = true ∧ s.inProgress = false ∧ s.d2 = none ∧ s.relays = []
  | .toGW pre c => Flight s pre ∧ s.d2 = none ∧ prepare pre = some c
  | .gwFailed pre => Flight s pre ∧ s.d2 = none
  | .gwMinted pre => Flight s pre ∧ s.d2.isSome = true
  | .onGW => s.d1.settling = false ∧ s.inProgress = false ∧ s.d2.isSome = true
  | .toL1 _ => s.d1.settling = false ∧ s.inProgress = false ∧ s.d2.isSome = true
  | .back => s.d1.settling = true ∧ s.inProgress = false ∧ s.d2.isSome = true

theorem pm_snapInv_initial (P : Params) : SnapInv (initial P) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem pm_depositsPaused_of_inProgress {P : Params} {s : St} (h : s.inProgress = true) :
    depositsPausedL1 P s = true := by
  unfold depositsPausedL1; rw [h, Bool.or_true]

/-- In flight, the L1 copy does not settle, deposits are paused and no relay is queued. -/
theorem pm_snap_flight {s : St} (hI : SnapInv s) (hf : s.phase.InFlight) :
    ∃ pre, s.phase.preBurn = some pre ∧ Flight s pre := by
  unfold SnapInv at hI
  unfold Phase.InFlight at hf
  cases hp : s.phase with
  | toGW pre c => rw [hp] at hI; exact ⟨pre, rfl, hI.1⟩
  | gwMinted pre => rw [hp] at hI; exact ⟨pre, rfl, hI.1⟩
  | gwFailed pre => rw [hp] at hI; exact ⟨pre, rfl, hI.1⟩
  | onL1 => rw [hp] at hf; cases hf
  | onGW => rw [hp] at hf; cases hf
  | toL1 c => rw [hp] at hf; cases hf
  | back => rw [hp] at hf; cases hf

theorem pm_snap_inProgress {s : St} (hI : SnapInv s) : s.inProgress = true ↔ s.phase.InFlight := by
  unfold SnapInv at hI
  unfold Phase.InFlight
  cases hp : s.phase with
  | onL1 => rw [hp] at hI; simp [Phase.preBurn, hI.2.1]
  | toGW pre c => rw [hp] at hI; simp [Phase.preBurn, hI.1.1]
  | gwMinted pre => rw [hp] at hI; simp [Phase.preBurn, hI.1.1]
  | gwFailed pre => rw [hp] at hI; simp [Phase.preBurn, hI.1.1]
  | onGW => rw [hp] at hI; simp [Phase.preBurn, hI.2.1]
  | toL1 c => rw [hp] at hI; simp [Phase.preBurn, hI.2.1]
  | back => rw [hp] at hI; simp [Phase.preBurn, hI.2.1]

theorem pm_snapInv_step {P : Params} {s s' : St} {op : Op} (hI : SnapInv s)
    (hs : step P s op = some s') : SnapInv s' := by
  cases op with
  | request h =>
    obtain ⟨_, hpd, t, _, rfl⟩ := pm_stepRequest hs
    unfold SnapInv at hI ⊢
    cases hp : s.phase with
    | onL1 =>
      rw [hp] at hI
      obtain ⟨h1, h2, h3, h4⟩ := hI
      exact ⟨h1, h2, h3, by simp [h1, h4]⟩
    | toGW pre c =>
      rw [hp] at hI
      rw [pm_depositsPaused_of_inProgress hI.1.1] at hpd; cases hpd
    | gwMinted pre =>
      rw [hp] at hI
      rw [pm_depositsPaused_of_inProgress hI.1.1] at hpd; cases hpd
    | gwFailed pre =>
      rw [hp] at hI
      rw [pm_depositsPaused_of_inProgress hI.1.1] at hpd; cases hpd
    | onGW => rw [hp] at hI; exact hI
    | toL1 c => rw [hp] at hI; exact hI
    | back =>
      rw [hp] at hI
      exact hI
  | l1Pipeline info b =>
    obtain ⟨hset, _, t, _, rfl⟩ := pm_stepL1Pipeline hs
    unfold SnapInv at hI ⊢
    cases hp : s.phase with
    | onL1 => rw [hp] at hI; exact hI
    | toGW pre c => rw [hp] at hI; rw [hI.1.2.1] at hset; cases hset
    | gwMinted pre => rw [hp] at hI; rw [hI.1.2.1] at hset; cases hset
    | gwFailed pre => rw [hp] at hI; rw [hI.1.2.1] at hset; cases hset
    | onGW => rw [hp] at hI; rw [hI.1] at hset; cases hset
    | toL1 c => rw [hp] at hI; rw [hI.1] at hset; cases hset
    | back => rw [hp] at hI; exact hI
  | pauseL1 =>
    obtain ⟨h0, ts, rfl⟩ := pm_stepPauseL1 hs
    unfold SnapInv at hI ⊢
    cases hp : s.phase with
    | onL1 => rw [hp] at hI; exact hI
    | toGW pre c => rw [hp] at hI; exact absurd (hI.1.2.2.2.2.2.1.symm.trans h0) hI.1.2.2.2.2.2.2.1
    | gwMinted pre => rw [hp] at hI; exact absurd (hI.1.2.2.2.2.2.1.symm.trans h0) hI.1.2.2.2.2.2.2.1
    | gwFailed pre => rw [hp] at hI; exact absurd (hI.1.2.2.2.2.2.1.symm.trans h0) hI.1.2.2.2.2.2.2.1
    | onGW => rw [hp] at hI; exact hI
    | toL1 c => rw [hp] at hI; exact hI
    | back => rw [hp] at hI; exact hI
  | unpauseL1 =>
    obtain ⟨_, hip, rfl⟩ := pm_stepUnpauseL1 hs
    unfold SnapInv at hI ⊢
    cases hp : s.phase with
    | onL1 => rw [hp] at hI; exact hI
    | toGW pre c => rw [hp] at hI; rw [hI.1.1] at hip; cases hip
    | gwMinted pre => rw [hp] at hI; rw [hI.1.1] at hip; cases hip
    | gwFailed pre => rw [hp] at hI; rw [hI.1.1] at hip; cases hip
    | onGW => rw [hp] at hI; exact hI
    | toL1 c => rw [hp] at hI; exact hI
    | back => rw [hp] at hI; exact hI
  | freezeL1 =>
    obtain rfl := pm_stepFreezeL1 hs
    exact hI
  | unfreezeL1 =>
    obtain rfl := pm_stepUnfreezeL1 hs
    exact hI
  | l1Burn =>
    obtain ⟨hp, _, hset, _, hwin, c, hc, rfl⟩ := pm_stepL1Burn hs
    unfold SnapInv at hI
    rw [hp] at hI
    obtain ⟨_, _, h3, h4⟩ := hI
    refine ⟨⟨rfl, rfl, hset, rfl, rfl, rfl, ?_, h4⟩, h3, hc⟩
    unfold inPausedWindow at hwin
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hwin
    exact hwin.1
  | gwMint =>
    obtain ⟨pre, c, t, b, hp, _, _, _, _, rfl⟩ := pm_stepGwMint hs
    unfold SnapInv at hI
    rw [hp] at hI
    exact ⟨hI.1, rfl⟩
  | gwMintFails =>
    obtain ⟨pre, c, hp, rfl⟩ := pm_stepGwMintFails hs
    unfold SnapInv at hI
    rw [hp] at hI
    exact ⟨hI.1, hI.2.1⟩
  | confirm success =>
    rcases pm_stepConfirm hs with ⟨pre, hp, _, rfl⟩ | ⟨pre, hp, _, _, rfl⟩
    · unfold SnapInv at hI
      rw [hp] at hI
      exact ⟨hI.1.2.1, rfl, hI.2⟩
    · unfold SnapInv at hI
      rw [hp] at hI
      exact ⟨rfl, rfl, hI.2, hI.1.2.2.2.2.2.2.2⟩
  | relay =>
    obtain ⟨h, rest, hr, hcase⟩ := pm_stepRelay hs
    unfold SnapInv at hI ⊢
    rcases hcase with ⟨rfl, _⟩ | ⟨d, t, hd, _, _, rfl⟩
    · cases hp : s.phase with
      | onL1 => rw [hp] at hI; rw [hI.2.2.2] at hr; cases hr
      | toGW pre c => rw [hp] at hI; rw [hI.1.2.2.2.2.2.2.2] at hr; cases hr
      | gwMinted pre => rw [hp] at hI; rw [hI.1.2.2.2.2.2.2.2] at hr; cases hr
      | gwFailed pre => rw [hp] at hI; rw [hI.1.2.2.2.2.2.2.2] at hr; cases hr
      | onGW => rw [hp] at hI; exact hI
      | toL1 c => rw [hp] at hI; exact hI
      | back => rw [hp] at hI; exact hI
    · cases hp : s.phase with
      | onL1 => rw [hp] at hI; rw [hI.2.2.2] at hr; cases hr
      | toGW pre c => rw [hp] at hI; rw [hI.1.2.2.2.2.2.2.2] at hr; cases hr
      | gwMinted pre => rw [hp] at hI; rw [hI.1.2.2.2.2.2.2.2] at hr; cases hr
      | gwFailed pre => rw [hp] at hI; rw [hI.1.2.2.2.2.2.2.2] at hr; cases hr
      | onGW => rw [hp] at hI; exact ⟨hI.1, hI.2.1, rfl⟩
      | toL1 c => rw [hp] at hI; exact ⟨hI.1, hI.2.1, rfl⟩
      | back => rw [hp] at hI; exact ⟨hI.1, hI.2.1, rfl⟩
  | gwPipeline info b =>
    obtain ⟨d, t, hd, _, _, _, rfl⟩ := pm_stepGwPipeline hs
    unfold SnapInv at hI ⊢
    cases hp : s.phase with
    | onL1 => rw [hp] at hI; rw [hI.2.2.1] at hd; cases hd
    | toGW pre c => rw [hp] at hI; rw [hI.2.1] at hd; cases hd
    | gwMinted pre => rw [hp] at hI; exact ⟨hI.1, rfl⟩
    | gwFailed pre => rw [hp] at hI; rw [hI.2] at hd; cases hd
    | onGW => rw [hp] at hI; exact ⟨hI.1, hI.2.1, rfl⟩
    | toL1 c => rw [hp] at hI; exact ⟨hI.1, hI.2.1, rfl⟩
    | back => rw [hp] at hI; exact ⟨hI.1, hI.2.1, rfl⟩
  | gwPause ts =>
    obtain ⟨d, hd, rfl⟩ := pm_stepGwPause hs
    unfold SnapInv at hI ⊢
    cases hp : s.phase with
    | onL1 => rw [hp] at hI; rw [hI.2.2.1] at hd; cases hd
    | toGW pre c => rw [hp] at hI; rw [hI.2.1] at hd; cases hd
    | gwMinted pre => rw [hp] at hI; exact ⟨hI.1, rfl⟩
    | gwFailed pre => rw [hp] at hI; rw [hI.2] at hd; cases hd
    | onGW => rw [hp] at hI; exact ⟨hI.1, hI.2.1, rfl⟩
    | toL1 c => rw [hp] at hI; exact ⟨hI.1, hI.2.1, rfl⟩
    | back => rw [hp] at hI; exact ⟨hI.1, hI.2.1, rfl⟩
  | freezeGW =>
    obtain ⟨d, hd, rfl⟩ := pm_stepFreezeGW hs
    unfold SnapInv at hI ⊢
    cases hp : s.phase with
    | onL1 => rw [hp] at hI; rw [hI.2.2.1] at hd; cases hd
    | toGW pre c => rw [hp] at hI; rw [hI.2.1] at hd; cases hd
    | gwMinted pre => rw [hp] at hI; exact ⟨hI.1, rfl⟩
    | gwFailed pre => rw [hp] at hI; rw [hI.2] at hd; cases hd
    | onGW => rw [hp] at hI; exact ⟨hI.1, hI.2.1, rfl⟩
    | toL1 c => rw [hp] at hI; exact ⟨hI.1, hI.2.1, rfl⟩
    | back => rw [hp] at hI; exact ⟨hI.1, hI.2.1, rfl⟩
  | unfreezeGW =>
    obtain ⟨d, hd, rfl⟩ := pm_stepUnfreezeGW hs
    unfold SnapInv at hI ⊢
    cases hp : s.phase with
    | onL1 => rw [hp] at hI; rw [hI.2.2.1] at hd; cases hd
    | toGW pre c => rw [hp] at hI; rw [hI.2.1] at hd; cases hd
    | gwMinted pre => rw [hp] at hI; exact ⟨hI.1, rfl⟩
    | gwFailed pre => rw [hp] at hI; rw [hI.2] at hd; cases hd
    | onGW => rw [hp] at hI; exact ⟨hI.1, hI.2.1, rfl⟩
    | toL1 c => rw [hp] at hI; exact ⟨hI.1, hI.2.1, rfl⟩
    | back => rw [hp] at hI; exact ⟨hI.1, hI.2.1, rfl⟩
  | gwBurn =>
    obtain ⟨d, c, hp, hd, _, _, _, _, rfl⟩ := pm_stepGwBurn hs
    unfold SnapInv at hI
    rw [hp] at hI
    exact ⟨hI.1, hI.2.1, rfl⟩
  | l1Mint =>
    obtain ⟨c, b, t, hp, _, _, _, _, _, _, _, rfl⟩ := pm_stepL1Mint hs
    unfold SnapInv at hI
    rw [hp] at hI
    exact ⟨rfl, hI.2.1, hI.2.2⟩
  | tick dt =>
    cases hs
    exact hI

theorem pm_snapInv_reach {P : Params} {ok : St → Op → Prop} {s : St} (h : Reach P ok s) :
    SnapInv s :=
  pm_steps_induct (fun _ _ _ hI _ hst => pm_snapInv_step hI hst) h (pm_snapInv_initial P)

/-! ## The invariant of every consistent run -/

/-- The gateway copy's tree is its leaves pushed from the setup state. -/
def Copy2 (P : Params) (s : St) (d : ChainDiamond) : Prop :=
  d.tree.startIndex = P.startIndex
  ∧ pushAll P.tree.node (setupTree P.tree) s.leaves2 = some d.tree.tree

/-- A gateway burn's commitment, against the processed operations `L`. -/
def CommitOK (P : Params) (c : ChainCommitment) (L : List UInt256) : Prop :=
  c.priorityTree.startIndex = P.startIndex ∧ c.priorityTree.nextLeafIndex = L.length
  ∧ c.priorityTree.unprocessedIndex = L.length
  ∧ (∃ zs, pushAll P.tree.node (setupTree P.tree) L =
      some { nextLeafIndex := L.length, sides := c.priorityTree.sides, zeros := zs })
  ∧ c.executed ≤ c.verified ∧ c.verified ≤ c.committed
  ∧ c.batchHashes.length = c.committed - c.executed + 1

/-- The gateway copy while the chain settles there or the return is in flight. -/
def GwFacts (P : Params) (s : St) (d : ChainDiamond) : Prop :=
  Copy2 P s d ∧ s.executed = s.leaves2.take d.tree.unprocessedIndex
  ∧ d.tree.unprocessedIndex ≤ s.leaves2.length
  ∧ s.d1.tree.unprocessedIndex ≤ d.tree.unprocessedIndex
  ∧ s.leaves2.take s.d1.tree.unprocessedIndex = s.log1.take s.d1.tree.unprocessedIndex
  ∧ s.leaves2.length + s.relays.length ≤ s.log1.length

/-- The processed operations and the gateway copy, by phase. -/
def GPhase (P : Params) (s : St) : Prop :=
  match s.phase with
  | .onL1 => s.executed = s.log1.take s.d1.tree.unprocessedIndex
  | .toGW _ _ => s.executed = s.log1 ∧ s.d1.tree.unprocessedIndex = s.log1.length
  | .gwFailed _ => s.executed = s.log1 ∧ s.d1.tree.unprocessedIndex = s.log1.length
  | .gwMinted _ => s.executed = s.log1 ∧ s.d1.tree.unprocessedIndex = s.log1.length
      ∧ ∃ d, s.d2 = some d ∧ Copy2 P s d ∧ d.settling = true ∧ s.leaves2 = s.log1
        ∧ d.tree.unprocessedIndex = s.log1.length
  | .onGW => ∃ d, s.d2 = some d ∧ d.settling = true ∧ GwFacts P s d
  | .toL1 c => ∃ d, s.d2 = some d ∧ d.settling = false ∧ GwFacts P s d ∧ CommitOK P c s.executed
  | .back => s.executed.length = s.d1.tree.unprocessedIndex
      ∧ ∃ d, s.d2 = some d ∧ d.settling = false

/-- The invariant of every consistent run. -/
structure GInv (P : Params) (s : St) : Prop where
  snap : SnapInv s
  start1 : s.d1.tree.startIndex = P.startIndex
  tree1 : pushAll P.tree.node (setupTree P.tree) s.log1 = some s.d1.tree.tree
  hist1 : ∀ r, s.d1.tree.historicalRoots r = true ↔
    ∃ p, p <+: s.log1 ∧ rootAfter P.tree p = some r
  bound1 : s.log1 ≠ [] → P.startIndex + s.log1.length < wordLimit
  u1 : s.d1.tree.unprocessedIndex ≤ s.log1.length
  execLen : s.executed.length ≤ s.log1.length
  phase : GPhase P s

theorem pm_prepare {d : ChainDiamond} {c : ChainCommitment} (h : prepare d = some c) :
    c.priorityTree = d.tree.getCommitment ∧ c.executed ≤ c.verified ∧ c.verified ≤ c.committed
    ∧ c.batchHashes.length = c.committed - c.executed + 1 := by
  unfold prepare at h
  split at h
  · rename_i hg
    cases h
    refine ⟨rfl, hg.1, hg.2, ?_⟩
    simp only [List.length_map, List.length_range]
  · cases h

theorem pm_ginv_initial (P : Params) : GInv P (initial P) where
  snap := pm_snapInv_initial P
  start1 := rfl
  tree1 := rfl
  hist1 := by
    intro r
    show markRoot (fun _ => false) 0 r = true ↔ _
    rw [pm_markRoot_true]
    constructor
    · rintro (rfl | h)
      · exact ⟨[], List.nil_prefix, rfl⟩
      · cases h
    · rintro ⟨p, hp, hr⟩
      rw [List.prefix_nil.mp hp] at hr
      exact Or.inl (Option.some.inj hr).symm
  bound1 := fun h => absurd rfl h
  u1 := le_refl 0
  execLen := le_refl 0
  phase := rfl

theorem pm_tree1_length {P : Params} {s : St} (hI : GInv P s) :
    s.d1.tree.tree.nextLeafIndex = s.log1.length :=
  (pm_pushAll_setup hI.tree1).2

theorem pm_copy2_length {P : Params} {s : St} {d : ChainDiamond} (h : Copy2 P s d) :
    d.tree.tree.nextLeafIndex = s.leaves2.length :=
  (pm_pushAll_setup h.2).2

/-- An L1 push extends the leaf list, the tree and the historical roots together. -/
theorem pm_l1_push {P : Params} {s : St} {h : UInt256} {t : PTree}
    (hI : GInv P s) (hw : mailboxWrite P.tree s.d1.tree h = some t) :
    t.startIndex = P.startIndex ∧ t.unprocessedIndex = s.d1.tree.unprocessedIndex
    ∧ pushAll P.tree.node (setupTree P.tree) (s.log1 ++ [h]) = some t.tree
    ∧ (∀ r, t.historicalRoots r = true ↔ ∃ p, p <+: s.log1 ++ [h] ∧ rootAfter P.tree p = some r)
    ∧ P.startIndex + (s.log1 ++ [h]).length < wordLimit := by
  obtain ⟨tree, r, hpush, rfl, hb⟩ := pm_mailboxWrite hw
  have hshape := (pm_pushAll_setup hI.tree1).1
  obtain ⟨_, hroot, hn⟩ := pm_push_shape hshape hpush
  have hall := pm_pushAll_snoc hI.tree1 hpush
  refine ⟨hI.start1, rfl, hall, ?_, ?_⟩
  · intro x
    show markRoot s.d1.tree.historicalRoots r x = true ↔ _
    rw [pm_markRoot_true, hI.hist1]
    constructor
    · rintro (rfl | ⟨p, hp, hpx⟩)
      · exact ⟨s.log1 ++ [h], List.prefix_refl _, by rw [pm_rootAfter_of_pushAll hall, hroot]⟩
      · exact ⟨p, hp.trans (List.prefix_append _ _), hpx⟩
    · rintro ⟨p, hp, hpx⟩
      rcases List.prefix_concat_iff.mp hp with rfl | hp'
      · left
        rw [pm_rootAfter_of_pushAll hall, hroot] at hpx
        exact (Option.some.inj hpx).symm
      · exact Or.inr ⟨p, hp', hpx⟩
  · have h1 := pm_tree1_length hI
    rw [List.length_append, List.length_singleton]
    show P.startIndex + (s.log1.length + 1) < wordLimit
    rw [← h1, ← hn, ← hI.start1]
    exact hb

/-- A gateway push extends the gateway leaf list and tree together. -/
theorem pm_gw_push {P : Params} {s : St} {d : ChainDiamond} {h : UInt256} {t : PTree}
    (hc : Copy2 P s d) (hw : mailboxWrite P.tree d.tree h = some t) :
    t.startIndex = d.tree.startIndex ∧ t.unprocessedIndex = d.tree.unprocessedIndex
    ∧ pushAll P.tree.node (setupTree P.tree) (s.leaves2 ++ [h]) = some t.tree := by
  obtain ⟨tree, r, hpush, rfl, _⟩ := pm_mailboxWrite hw
  exact ⟨rfl, rfl, pm_pushAll_snoc hc.2 hpush⟩

/-- On the gateway copy, a push of the next L1 leaf succeeds. -/
theorem pm_gw_push_succeeds {P : Params} {s : St} {d : ChainDiamond} {h : UInt256}
    (hI : GInv P s) (hc : Copy2 P s d) (hpre : s.leaves2 ++ [h] <+: s.log1) :
    ∃ t, mailboxWrite P.tree d.tree h = some t := by
  obtain ⟨t'', ht''⟩ := pm_pushAll_of_prefix hI.tree1 hpre
  obtain ⟨t₁, r, h1, h2⟩ := pm_pushAll_snoc_inv ht''
  rw [hc.2] at h1
  cases h1
  have hshape := (pm_pushAll_setup ht'').2
  have hne : s.log1 ≠ [] := by
    intro hnil
    rw [hnil] at hpre
    have := hpre.length_le
    simp at this
  have hb := hI.bound1 hne
  have hlen := hpre.length_le
  refine ⟨_, pm_mailboxWrite_of_push h2 ?_⟩
  rw [hc.1, hshape]
  omega

/-- Changing the gateway copy without changing its tree or settlement field keeps `GPhase`. -/
theorem pm_gphase_d2 {P : Params} {s : St} {d d' : ChainDiamond} (hd : s.d2 = some d)
    (htree : d'.tree = d.tree) (hset : d'.settling = d.settling) (h : GPhase P s) :
    GPhase P { s with d2 := some d' } := by
  unfold GPhase at h ⊢
  cases hp : s.phase with
  | onL1 => rw [hp] at h; exact h
  | toGW pre c => rw [hp] at h; exact h
  | gwFailed pre => rw [hp] at h; exact h
  | gwMinted pre =>
    rw [hp] at h
    obtain ⟨h1, h2, d0, hd0, hc, hs, hl, hu⟩ := h
    rw [hd] at hd0; cases hd0
    exact ⟨h1, h2, d', rfl, by unfold Copy2 at hc ⊢; rw [htree]; exact hc, by rw [hset]; exact hs,
      hl, by rw [htree]; exact hu⟩
  | onGW =>
    rw [hp] at h
    obtain ⟨d0, hd0, hs, hg⟩ := h
    rw [hd] at hd0; cases hd0
    refine ⟨d', rfl, by rw [hset]; exact hs, ?_⟩
    unfold GwFacts Copy2 at hg ⊢
    rw [htree]
    exact hg
  | toL1 c =>
    rw [hp] at h
    obtain ⟨d0, hd0, hs, hg, hco⟩ := h
    rw [hd] at hd0; cases hd0
    refine ⟨d', rfl, by rw [hset]; exact hs, ?_, hco⟩
    unfold GwFacts Copy2 at hg ⊢
    rw [htree]
    exact hg
  | back =>
    rw [hp] at h
    obtain ⟨h1, d0, hd0, hs⟩ := h
    rw [hd] at hd0; cases hd0
    exact ⟨h1, d', rfl, by rw [hset]; exact hs⟩

theorem pm_ginv_step {P : Params} {s s' : St} {op : Op} (hI : GInv P s)
    (hok : ConsistentProcessing s op) (hs : step P s op = some s') : GInv P s' := by
  have hsnap := pm_snapInv_step hI.snap hs
  have hsn := hI.snap
  have hph := hI.phase
  unfold SnapInv at hsn
  unfold GPhase at hph
  cases op with
  | request h =>
    obtain ⟨_, hpd, t, hw, rfl⟩ := pm_stepRequest hs
    obtain ⟨hst, hu, htree, hhist, hb⟩ := pm_l1_push hI hw
    have hu1 := hI.u1
    have hel := hI.execLen
    refine ⟨hsnap, hst, htree, hhist, fun _ => hb, ?_, ?_, ?_⟩
    · show t.unprocessedIndex ≤ (s.log1 ++ [h]).length
      rw [hu, List.length_append]; omega
    · show s.executed.length ≤ (s.log1 ++ [h]).length
      rw [List.length_append]; omega
    · unfold GPhase
      cases hp : s.phase with
      | onL1 =>
        rw [hp] at hph
        show s.executed = (s.log1 ++ [h]).take t.unprocessedIndex
        rw [hu, List.take_append_of_le_length hu1]
        exact hph
      | toGW pre c =>
        rw [hp] at hsn
        rw [pm_depositsPaused_of_inProgress hsn.1.1] at hpd; cases hpd
      | gwMinted pre =>
        rw [hp] at hsn
        rw [pm_depositsPaused_of_inProgress hsn.1.1] at hpd; cases hpd
      | gwFailed pre =>
        rw [hp] at hsn
        rw [pm_depositsPaused_of_inProgress hsn.1.1] at hpd; cases hpd
      | onGW =>
        rw [hp] at hph hsn
        obtain ⟨d, hd, hs2, hc, he, hdu, h1u, htk, hrl⟩ := hph
        refine ⟨d, hd, hs2, hc, he, hdu, by rw [hu]; exact h1u, ?_, ?_⟩
        · show s.leaves2.take t.unprocessedIndex = (s.log1 ++ [h]).take t.unprocessedIndex
          rw [hu, List.take_append_of_le_length hu1]; exact htk
        · show s.leaves2.length + (if s.d1.settling then s.relays else s.relays ++ [h]).length
            ≤ (s.log1 ++ [h]).length
          rw [hsn.1]
          simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton]
          omega
      | toL1 c =>
        rw [hp] at hph hsn
        obtain ⟨d, hd, hs2, ⟨hc, he, hdu, h1u, htk, hrl⟩, hco⟩ := hph
        refine ⟨d, hd, hs2, ⟨hc, he, hdu, by rw [hu]; exact h1u, ?_, ?_⟩, hco⟩
        · show s.leaves2.take t.unprocessedIndex = (s.log1 ++ [h]).take t.unprocessedIndex
          rw [hu, List.take_append_of_le_length hu1]; exact htk
        · show s.leaves2.length + (if s.d1.settling then s.relays else s.relays ++ [h]).length
            ≤ (s.log1 ++ [h]).length
          rw [hsn.1]
          simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton]
          omega
      | back =>
        rw [hp] at hph
        obtain ⟨h1, hd⟩ := hph
        exact ⟨by rw [hu]; exact h1, hd⟩
  | l1Pipeline info b =>
    obtain ⟨hset, _, t, hpb, rfl⟩ := pm_stepL1Pipeline hs
    have ht := pm_processBatch hpb
    have hcons : s.d1.tree.unprocessedIndex + info.itemHashes.length ≤ s.log1.length := by
      have := hok; unfold ConsistentProcessing at this; rw [pm_tree1_length hI] at this; exact this
    have hsl : (slice s.log1 s.d1.tree.unprocessedIndex info.itemHashes.length).length
        = info.itemHashes.length := by
      unfold slice; rw [List.length_take, List.length_drop]; omega
    subst ht
    refine ⟨hsnap, hI.start1, hI.tree1, hI.hist1, hI.bound1, hcons, ?_, ?_⟩
    · show (s.executed ++ slice s.log1 s.d1.tree.unprocessedIndex info.itemHashes.length).length
        ≤ s.log1.length
      cases hp : s.phase with
      | onL1 =>
        rw [hp] at hph
        rw [hph, List.length_append, hsl, List.length_take]; omega
      | back =>
        rw [hp] at hph
        rw [List.length_append, hsl, hph.1]; exact hcons
      | toGW pre c => rw [hp] at hsn; rw [hsn.1.2.1] at hset; cases hset
      | gwMinted pre => rw [hp] at hsn; rw [hsn.1.2.1] at hset; cases hset
      | gwFailed pre => rw [hp] at hsn; rw [hsn.1.2.1] at hset; cases hset
      | onGW => rw [hp] at hsn; rw [hsn.1] at hset; cases hset
      | toL1 c => rw [hp] at hsn; rw [hsn.1] at hset; cases hset
    · unfold GPhase
      cases hp : s.phase with
      | onL1 =>
        rw [hp] at hph
        show s.executed ++ slice s.log1 s.d1.tree.unprocessedIndex info.itemHashes.length
          = s.log1.take (s.d1.tree.unprocessedIndex + info.itemHashes.length)
        rw [hph, List.take_add]; rfl
      | back =>
        rw [hp] at hph
        obtain ⟨h1, hd⟩ := hph
        refine ⟨?_, hd⟩
        show (s.executed ++ slice s.log1 s.d1.tree.unprocessedIndex info.itemHashes.length).length
          = s.d1.tree.unprocessedIndex + info.itemHashes.length
        rw [List.length_append, hsl, h1]
      | toGW pre c => rw [hp] at hsn; rw [hsn.1.2.1] at hset; cases hset
      | gwMinted pre => rw [hp] at hsn; rw [hsn.1.2.1] at hset; cases hset
      | gwFailed pre => rw [hp] at hsn; rw [hsn.1.2.1] at hset; cases hset
      | onGW => rw [hp] at hsn; rw [hsn.1] at hset; cases hset
      | toL1 c => rw [hp] at hsn; rw [hsn.1] at hset; cases hset
  | pauseL1 =>
    obtain ⟨_, ts, rfl⟩ := pm_stepPauseL1 hs
    exact ⟨hsnap, hI.start1, hI.tree1, hI.hist1, hI.bound1, hI.u1, hI.execLen, hI.phase⟩
  | unpauseL1 =>
    obtain ⟨_, _, rfl⟩ := pm_stepUnpauseL1 hs
    exact ⟨hsnap, hI.start1, hI.tree1, hI.hist1, hI.bound1, hI.u1, hI.execLen, hI.phase⟩
  | freezeL1 =>
    obtain rfl := pm_stepFreezeL1 hs
    exact ⟨hsnap, hI.start1, hI.tree1, hI.hist1, hI.bound1, hI.u1, hI.execLen, hI.phase⟩
  | unfreezeL1 =>
    obtain rfl := pm_stepUnfreezeL1 hs
    exact ⟨hsnap, hI.start1, hI.tree1, hI.hist1, hI.bound1, hI.u1, hI.execLen, hI.phase⟩
  | l1Burn =>
    obtain ⟨hp, _, _, hsize, _, c, _, rfl⟩ := pm_stepL1Burn hs
    refine ⟨hsnap, hI.start1, hI.tree1, hI.hist1, hI.bound1, hI.u1, hI.execLen, ?_⟩
    rw [hp] at hph
    have hu : s.d1.tree.unprocessedIndex = s.log1.length := by
      rw [pm_getSize_zero hsize, pm_tree1_length hI]
    show s.executed = s.log1 ∧ s.d1.tree.unprocessedIndex = s.log1.length
    rw [hph, hu, List.take_length]
    exact ⟨rfl, rfl⟩
  | gwMint =>
    obtain ⟨pre, c, t, b, hp, _, _, hinit, _, rfl⟩ := pm_stepGwMint hs
    refine ⟨hsnap, hI.start1, hI.tree1, hI.hist1, hI.bound1, hI.u1, hI.execLen, ?_⟩
    rw [hp] at hph hsn
    obtain ⟨he, hu⟩ := hph
    obtain ⟨⟨_, _, _, htr, _, _, _, _⟩, _, hprep⟩ := hsn
    obtain ⟨hct, _, _, _⟩ := pm_prepare hprep
    obtain ⟨hts, htu, htt⟩ := pm_initFromCommitment hinit
    rw [hct] at hts htu htt
    have hshape := (pm_pushAll_setup hI.tree1).1
    refine ⟨he, hu, _, rfl, ⟨?_, ?_⟩, rfl, rfl, ?_⟩
    · show t.startIndex = P.startIndex
      rw [hts]; show pre.tree.startIndex = P.startIndex; rw [← htr]; exact hI.start1
    · show pushAll P.tree.node (setupTree P.tree) s.log1 = some t.tree
      rw [htt]
      show pushAll P.tree.node (setupTree P.tree) s.log1 = some
        { nextLeafIndex := pre.tree.tree.nextLeafIndex, sides := pre.tree.tree.sides,
          zeros := PTree.zeroCascade P.tree pre.tree.tree.sides.length }
      rw [← htr, pm_rebuild hshape]
      exact hI.tree1
    · show t.unprocessedIndex = s.log1.length
      rw [htu]; show pre.tree.unprocessedIndex = s.log1.length; rw [← htr]; exact hu
  | gwMintFails =>
    obtain ⟨pre, c, hp, rfl⟩ := pm_stepGwMintFails hs
    refine ⟨hsnap, hI.start1, hI.tree1, hI.hist1, hI.bound1, hI.u1, hI.execLen, ?_⟩
    rw [hp] at hph
    exact hph
  | confirm success =>
    rcases pm_stepConfirm hs with ⟨pre, hp, _, rfl⟩ | ⟨pre, hp, _, _, rfl⟩
    · refine ⟨hsnap, hI.start1, hI.tree1, hI.hist1, hI.bound1, hI.u1, hI.execLen, ?_⟩
      rw [hp] at hph hsn
      obtain ⟨he, hu, d, hd, hc, hs2, hl, hdu⟩ := hph
      have hrel := hsn.1.2.2.2.2.2.2.2
      refine ⟨d, hd, hs2, hc, ?_, ?_, ?_, ?_, ?_⟩
      · show s.executed = s.leaves2.take d.tree.unprocessedIndex
        rw [he, hl, hdu, List.take_length]
      · show d.tree.unprocessedIndex ≤ s.leaves2.length
        rw [hl, hdu]
      · show s.d1.tree.unprocessedIndex ≤ d.tree.unprocessedIndex
        rw [hu, hdu]
      · show s.leaves2.take s.d1.tree.unprocessedIndex = s.log1.take s.d1.tree.unprocessedIndex
        rw [hl]
      · show s.leaves2.length + s.relays.length ≤ s.log1.length
        rw [hl, hrel, List.length_nil, Nat.add_zero]
    · refine ⟨hsnap, hI.start1, hI.tree1, hI.hist1, hI.bound1, hI.u1, hI.execLen, ?_⟩
      rw [hp] at hph
      show s.executed = s.log1.take s.d1.tree.unprocessedIndex
      rw [hph.1, hph.2, List.take_length]
  | relay =>
    obtain ⟨h, rest, hr, hcase⟩ := pm_stepRelay hs
    have hel := hI.execLen
    rcases hcase with ⟨rfl, _⟩ | ⟨d, t, hd, _, hw, rfl⟩
    · refine ⟨hsnap, hI.start1, hI.tree1, hI.hist1, hI.bound1, hI.u1, hI.execLen, ?_⟩
      unfold GPhase
      cases hp : s.phase with
      | onL1 => rw [hp] at hsn; rw [hsn.2.2.2] at hr; cases hr
      | toGW pre c => rw [hp] at hsn; rw [hsn.1.2.2.2.2.2.2.2] at hr; cases hr
      | gwMinted pre => rw [hp] at hsn; rw [hsn.1.2.2.2.2.2.2.2] at hr; cases hr
      | gwFailed pre => rw [hp] at hsn; rw [hsn.1.2.2.2.2.2.2.2] at hr; cases hr
      | onGW =>
        rw [hp] at hph
        obtain ⟨d, hd, hs2, hc, he, hdu, h1u, htk, hrl⟩ := hph
        refine ⟨d, hd, hs2, hc, he, hdu, h1u, htk, ?_⟩
        show s.leaves2.length + rest.length ≤ s.log1.length
        rw [hr, List.length_cons] at hrl; omega
      | toL1 c =>
        rw [hp] at hph
        obtain ⟨d, hd, hs2, ⟨hc, he, hdu, h1u, htk, hrl⟩, hco⟩ := hph
        refine ⟨d, hd, hs2, ⟨hc, he, hdu, h1u, htk, ?_⟩, hco⟩
        show s.leaves2.length + rest.length ≤ s.log1.length
        rw [hr, List.length_cons] at hrl; omega
      | back => rw [hp] at hph; exact hph
    · refine ⟨hsnap, hI.start1, hI.tree1, hI.hist1, hI.bound1, hI.u1, hI.execLen, ?_⟩
      unfold GPhase
      cases hp : s.phase with
      | onL1 => rw [hp] at hsn; rw [hsn.2.2.2] at hr; cases hr
      | toGW pre c => rw [hp] at hsn; rw [hsn.1.2.2.2.2.2.2.2] at hr; cases hr
      | gwMinted pre => rw [hp] at hsn; rw [hsn.1.2.2.2.2.2.2.2] at hr; cases hr
      | gwFailed pre => rw [hp] at hsn; rw [hsn.1.2.2.2.2.2.2.2] at hr; cases hr
      | onGW =>
        rw [hp] at hph
        obtain ⟨d0, hd0, hs2, hc, he, hdu, h1u, htk, hrl⟩ := hph
        rw [hd] at hd0; cases hd0
        obtain ⟨hts, htu, htt⟩ := pm_gw_push hc hw
        refine ⟨{ d with tree := t }, rfl, hs2, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
        · show t.startIndex = P.startIndex; rw [hts]; exact hc.1
        · exact htt
        · show s.executed = (s.leaves2 ++ [h]).take t.unprocessedIndex
          rw [htu, List.take_append_of_le_length hdu]; exact he
        · show t.unprocessedIndex ≤ (s.leaves2 ++ [h]).length
          rw [htu, List.length_append]; omega
        · show s.d1.tree.unprocessedIndex ≤ t.unprocessedIndex
          rw [htu]; exact h1u
        · show (s.leaves2 ++ [h]).take s.d1.tree.unprocessedIndex
            = s.log1.take s.d1.tree.unprocessedIndex
          rw [List.take_append_of_le_length (h1u.trans hdu)]; exact htk
        · show (s.leaves2 ++ [h]).length + rest.length ≤ s.log1.length
          rw [hr, List.length_cons] at hrl
          rw [List.length_append, List.length_singleton]; omega
      | toL1 c =>
        rw [hp] at hph
        obtain ⟨d0, hd0, hs2, ⟨hc, he, hdu, h1u, htk, hrl⟩, hco⟩ := hph
        rw [hd] at hd0; cases hd0
        obtain ⟨hts, htu, htt⟩ := pm_gw_push hc hw
        refine ⟨{ d with tree := t }, rfl, hs2, ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, hco⟩
        · show t.startIndex = P.startIndex; rw [hts]; exact hc.1
        · exact htt
        · show s.executed = (s.leaves2 ++ [h]).take t.unprocessedIndex
          rw [htu, List.take_append_of_le_length hdu]; exact he
        · show t.unprocessedIndex ≤ (s.leaves2 ++ [h]).length
          rw [htu, List.length_append]; omega
        · show s.d1.tree.unprocessedIndex ≤ t.unprocessedIndex
          rw [htu]; exact h1u
        · show (s.leaves2 ++ [h]).take s.d1.tree.unprocessedIndex
            = s.log1.take s.d1.tree.unprocessedIndex
          rw [List.take_append_of_le_length (h1u.trans hdu)]; exact htk
        · show (s.leaves2 ++ [h]).length + rest.length ≤ s.log1.length
          rw [hr, List.length_cons] at hrl
          rw [List.length_append, List.length_singleton]; omega
      | back =>
        rw [hp] at hph
        obtain ⟨h1, d0, hd0, hs2⟩ := hph
        rw [hd] at hd0; cases hd0
        exact ⟨h1, { d with tree := t }, rfl, hs2⟩
  | gwPipeline info b =>
    obtain ⟨d, t, hd, hset, _, hpb, rfl⟩ := pm_stepGwPipeline hs
    have ht := pm_processBatch hpb
    have hcons : d.tree.unprocessedIndex + info.itemHashes.length ≤ d.tree.tree.nextLeafIndex := by
      have := hok; unfold ConsistentProcessing at this; exact this d hd
    subst ht
    refine ⟨hsnap, hI.start1, hI.tree1, hI.hist1, hI.bound1, hI.u1, ?_, ?_⟩
    · show (s.executed ++ slice s.leaves2 d.tree.unprocessedIndex info.itemHashes.length).length
        ≤ s.log1.length
      cases hp : s.phase with
      | onL1 => rw [hp] at hsn; rw [hsn.2.2.1] at hd; cases hd
      | toGW pre c => rw [hp] at hsn; rw [hsn.2.1] at hd; cases hd
      | gwFailed pre => rw [hp] at hsn; rw [hsn.2] at hd; cases hd
      | gwMinted pre =>
        rw [hp] at hph
        obtain ⟨he, _, d0, hd0, hc, _, hl, hdu⟩ := hph
        rw [hd] at hd0; cases hd0
        rw [pm_copy2_length hc, hl, hdu] at hcons
        have h0 : info.itemHashes.length = 0 := by omega
        rw [h0, he]
        unfold slice
        rw [List.take_zero, List.append_nil]
      | onGW =>
        rw [hp] at hph
        obtain ⟨d0, hd0, _, hc, he, hdu, _, _, hrl⟩ := hph
        rw [hd] at hd0; cases hd0
        rw [pm_copy2_length hc] at hcons
        rw [he]
        unfold slice
        rw [← List.take_add, List.length_take]
        omega
      | toL1 c =>
        rw [hp] at hph
        obtain ⟨d0, hd0, hs2, _⟩ := hph
        rw [hd] at hd0; cases hd0
        rw [hs2] at hset; cases hset
      | back =>
        rw [hp] at hph
        obtain ⟨_, d0, hd0, hs2⟩ := hph
        rw [hd] at hd0; cases hd0
        rw [hs2] at hset; cases hset
    · unfold GPhase
      cases hp : s.phase with
      | onL1 => rw [hp] at hsn; rw [hsn.2.2.1] at hd; cases hd
      | toGW pre c => rw [hp] at hsn; rw [hsn.2.1] at hd; cases hd
      | gwFailed pre => rw [hp] at hsn; rw [hsn.2] at hd; cases hd
      | gwMinted pre =>
        rw [hp] at hph
        obtain ⟨he, hu, d0, hd0, hc, hs2, hl, hdu⟩ := hph
        rw [hd] at hd0; cases hd0
        rw [pm_copy2_length hc, hl, hdu] at hcons
        have h0 : info.itemHashes.length = 0 := by omega
        refine ⟨?_, hu, _, rfl, hc, hs2, hl, ?_⟩
        · show s.executed ++ slice s.leaves2 d.tree.unprocessedIndex info.itemHashes.length = s.log1
          rw [h0, he]; unfold slice; rw [List.take_zero, List.append_nil]
        · show d.tree.unprocessedIndex + info.itemHashes.length = s.log1.length
          rw [h0, Nat.add_zero, hdu]
      | onGW =>
        rw [hp] at hph
        obtain ⟨d0, hd0, hs2, hc, he, hdu, h1u, htk, hrl⟩ := hph
        rw [hd] at hd0; cases hd0
        rw [pm_copy2_length hc] at hcons
        refine ⟨_, rfl, hs2, hc, ?_, ?_, ?_, htk, hrl⟩
        · show s.executed ++ slice s.leaves2 d.tree.unprocessedIndex info.itemHashes.length
            = s.leaves2.take (d.tree.unprocessedIndex + info.itemHashes.length)
          rw [he, List.take_add]; rfl
        · show d.tree.unprocessedIndex + info.itemHashes.length ≤ s.leaves2.length
          exact hcons
        · show s.d1.tree.unprocessedIndex ≤ d.tree.unprocessedIndex + info.itemHashes.length
          omega
      | toL1 c =>
        rw [hp] at hph
        obtain ⟨d0, hd0, hs2, _⟩ := hph
        rw [hd] at hd0; cases hd0
        rw [hs2] at hset; cases hset
      | back =>
        rw [hp] at hph
        obtain ⟨_, d0, hd0, hs2⟩ := hph
        rw [hd] at hd0; cases hd0
        rw [hs2] at hset; cases hset
  | gwPause ts =>
    obtain ⟨d, hd, rfl⟩ := pm_stepGwPause hs
    exact ⟨hsnap, hI.start1, hI.tree1, hI.hist1, hI.bound1, hI.u1, hI.execLen,
      pm_gphase_d2 hd rfl rfl hI.phase⟩
  | freezeGW =>
    obtain ⟨d, hd, rfl⟩ := pm_stepFreezeGW hs
    exact ⟨hsnap, hI.start1, hI.tree1, hI.hist1, hI.bound1, hI.u1, hI.execLen,
      pm_gphase_d2 hd rfl rfl hI.phase⟩
  | unfreezeGW =>
    obtain ⟨d, hd, rfl⟩ := pm_stepUnfreezeGW hs
    exact ⟨hsnap, hI.start1, hI.tree1, hI.hist1, hI.bound1, hI.u1, hI.execLen,
      pm_gphase_d2 hd rfl rfl hI.phase⟩
  | gwBurn =>
    obtain ⟨d, c, hp, hd, _, _, hsize, hprep, rfl⟩ := pm_stepGwBurn hs
    refine ⟨hsnap, hI.start1, hI.tree1, hI.hist1, hI.bound1, hI.u1, hI.execLen, ?_⟩
    rw [hp] at hph
    obtain ⟨d0, hd0, _, hg⟩ := hph
    rw [hd] at hd0; cases hd0
    obtain ⟨hc, he, hdu, h1u, htk, hrl⟩ := hg
    obtain ⟨hct, hb1, hb2, hb3⟩ := pm_prepare hprep
    have hn := pm_copy2_length hc
    have hu : d.tree.unprocessedIndex = s.leaves2.length := by
      rw [pm_getSize_zero hsize, hn]
    have hex : s.executed = s.leaves2 := by rw [he, hu, List.take_length]
    refine ⟨{ d with settling := false }, rfl, rfl, ⟨hc, he, hdu, h1u, htk, hrl⟩, ?_⟩
    unfold CommitOK
    rw [hct]
    refine ⟨hc.1, ?_, ?_, ⟨d.tree.tree.zeros, ?_⟩, hb1, hb2, hb3⟩
    · show d.tree.tree.nextLeafIndex = s.executed.length
      rw [hn, hex]
    · show d.tree.unprocessedIndex = s.executed.length
      rw [hu, hex]
    · show pushAll P.tree.node (setupTree P.tree) s.executed
        = some { nextLeafIndex := s.executed.length, sides := d.tree.tree.sides,
                 zeros := d.tree.tree.zeros }
      rw [hex, hc.2, ← hn]
  | l1Mint =>
    obtain ⟨c, b, t, hp, _, _, _, _, _, _, hre, rfl⟩ := pm_stepL1Mint hs
    obtain ⟨_, _, _, rfl⟩ := pm_l1Reinit hre
    rw [hp] at hph
    obtain ⟨d, hd, hs2, _, hco⟩ := hph
    have hcu : c.priorityTree.unprocessedIndex = s.executed.length := hco.2.2.1
    refine ⟨hsnap, hI.start1, hI.tree1, hI.hist1, hI.bound1, ?_, hI.execLen, ?_⟩
    · show c.priorityTree.unprocessedIndex ≤ s.log1.length
      rw [hcu]; exact hI.execLen
    · exact ⟨hcu.symm, d, hd, hs2⟩
  | tick dt =>
    cases hs
    exact ⟨hsnap, hI.start1, hI.tree1, hI.hist1, hI.bound1, hI.u1, hI.execLen, hI.phase⟩

theorem pm_ginv_reach {P : Params} {s : St} (h : Reach P ConsistentProcessing s) : GInv P s :=
  pm_steps_induct (fun _ _ _ hI hok hst => pm_ginv_step hI hok hst) h (pm_ginv_initial P)

theorem pm_ginv_reach_honest {P : Params} {s : St} (h : Reach P Honest s) : GInv P s :=
  pm_ginv_reach (pm_steps_mono (fun _ _ hok => hok.1) h)

/-! ## The mirror invariant of every honest run -/

/-- The gateway leaves followed by the pending relays are the L1 leaves until the return; after
it, the processed operations are the L1 leaves below the L1 unprocessed index. -/
def MInv (s : St) : Prop :=
  match s.phase with
  | .gwMinted _ => s.leaves2 ++ s.relays = s.log1
  | .onGW => s.leaves2 ++ s.relays = s.log1
  | .toL1 _ => s.leaves2 ++ s.relays = s.log1
  | .back => s.executed = s.log1.take s.d1.tree.unprocessedIndex
  | .onL1 => True
  | .toGW _ _ => True
  | .gwFailed _ => True

theorem pm_minv_step {P : Params} {s s' : St} {op : Op} (hG : GInv P s) (hM : MInv s)
    (hok : Honest s op) (hs : step P s op = some s') : MInv s' := by
  have hsn := hG.snap
  have hph := hG.phase
  unfold SnapInv at hsn
  unfold GPhase at hph
  unfold MInv at hM
  cases op with
  | request h =>
    obtain ⟨_, hpd, t, hw, rfl⟩ := pm_stepRequest hs
    obtain ⟨_, hu, _, _, _⟩ := pm_l1_push hG hw
    unfold MInv
    cases hp : s.phase with
    | onL1 => trivial
    | toGW pre c => trivial
    | gwFailed pre => trivial
    | gwMinted pre =>
      rw [hp] at hsn
      rw [pm_depositsPaused_of_inProgress hsn.1.1] at hpd; cases hpd
    | onGW =>
      rw [hp] at hsn hM
      show s.leaves2 ++ (if s.d1.settling then s.relays else s.relays ++ [h]) = s.log1 ++ [h]
      rw [hsn.1, ← hM]
      simp
    | toL1 c =>
      rw [hp] at hsn hM
      show s.leaves2 ++ (if s.d1.settling then s.relays else s.relays ++ [h]) = s.log1 ++ [h]
      rw [hsn.1, ← hM]
      simp
    | back =>
      rw [hp] at hM
      show s.executed = (s.log1 ++ [h]).take t.unprocessedIndex
      rw [hu, List.take_append_of_le_length hG.u1]
      exact hM
  | l1Pipeline info b =>
    obtain ⟨_, _, t, hpb, rfl⟩ := pm_stepL1Pipeline hs
    have ht := pm_processBatch hpb
    subst ht
    have hcons : s.d1.tree.unprocessedIndex + info.itemHashes.length ≤ s.log1.length := by
      have := hok.1; unfold ConsistentProcessing at this; rw [pm_tree1_length hG] at this; exact this
    unfold MInv
    cases hp : s.phase with
    | back =>
      rw [hp] at hM
      show s.executed ++ slice s.log1 s.d1.tree.unprocessedIndex info.itemHashes.length
        = s.log1.take (s.d1.tree.unprocessedIndex + info.itemHashes.length)
      rw [hM, List.take_add]; rfl
    | onL1 => trivial
    | toGW pre c => trivial
    | gwFailed pre => trivial
    | gwMinted pre => rw [hp] at hM; exact hM
    | onGW => rw [hp] at hM; exact hM
    | toL1 c => rw [hp] at hM; exact hM
  | pauseL1 =>
    obtain ⟨_, ts, rfl⟩ := pm_stepPauseL1 hs
    exact hM
  | unpauseL1 =>
    obtain ⟨_, _, rfl⟩ := pm_stepUnpauseL1 hs
    exact hM
  | freezeL1 =>
    obtain rfl := pm_stepFreezeL1 hs
    exact hM
  | unfreezeL1 =>
    obtain rfl := pm_stepUnfreezeL1 hs
    exact hM
  | l1Burn =>
    obtain ⟨_, _, _, _, _, c, _, rfl⟩ := pm_stepL1Burn hs
    trivial
  | gwMint =>
    obtain ⟨pre, c, t, b, hp, _, _, _, _, rfl⟩ := pm_stepGwMint hs
    rw [hp] at hsn
    show s.log1 ++ s.relays = s.log1
    rw [hsn.1.2.2.2.2.2.2.2, List.append_nil]
  | gwMintFails =>
    obtain ⟨pre, c, _, rfl⟩ := pm_stepGwMintFails hs
    trivial
  | confirm success =>
    rcases pm_stepConfirm hs with ⟨pre, hp, _, rfl⟩ | ⟨pre, hp, _, _, rfl⟩
    · rw [hp] at hM
      exact hM
    · trivial
  | relay =>
    obtain ⟨h, rest, hr, hcase⟩ := pm_stepRelay hs
    -- With a relay pending, the chain is on the gateway, its return is in flight, or it is back.
    have hrel : s.phase = .onGW ∨ (∃ c, s.phase = .toL1 c) ∨ s.phase = .back := by
      cases hp : s.phase with
      | onL1 => rw [hp] at hsn; rw [hsn.2.2.2] at hr; cases hr
      | toGW pre c => rw [hp] at hsn; rw [hsn.1.2.2.2.2.2.2.2] at hr; cases hr
      | gwFailed pre => rw [hp] at hsn; rw [hsn.1.2.2.2.2.2.2.2] at hr; cases hr
      | gwMinted pre => rw [hp] at hsn; rw [hsn.1.2.2.2.2.2.2.2] at hr; cases hr
      | onGW => exact Or.inl rfl
      | toL1 c => exact Or.inr (Or.inl ⟨c, rfl⟩)
      | back => exact Or.inr (Or.inr rfl)
    -- FREEZE-ORDER, before the return.
    have hfo : s.phase ≠ .back → ∀ d, s.d2 = some d → d.frozen = false := by
      intro hnb
      have h2 : s.phase = .back ∨ ∀ d, s.d2 = some d → d.frozen = false := hok.2
      rcases h2 with hb | hf
      · exact absurd hb hnb
      · exact hf
    -- Before the return, the relay's push on the gateway copy succeeds.
    have hnodrop : ∀ (d : ChainDiamond), s.phase ≠ .back → s.d2 = some d → Copy2 P s d →
        s.leaves2 ++ s.relays = s.log1 →
        (s.d2 = none ∨ ∃ d, s.d2 = some d
          ∧ (d.frozen = true ∨ (d.frozen = false ∧ mailboxWrite P.tree d.tree h = none))) → False := by
      intro d0 hnb hd0 hc hmir hdrop
      have hpre : s.leaves2 ++ [h] <+: s.log1 := by
        rw [← hmir, hr]; exact ⟨rest, by simp⟩
      rcases hdrop with hn | ⟨d, hd, hf | ⟨_, hw⟩⟩
      · rw [hd0] at hn; cases hn
      · have := hfo hnb d hd; rw [this] at hf; cases hf
      · rw [hd0] at hd; cases hd
        obtain ⟨t, ht⟩ := pm_gw_push_succeeds hG hc hpre
        rw [ht] at hw; cases hw
    rcases hcase with ⟨rfl, hdrop⟩ | ⟨d, t, _, _, _, rfl⟩
    · unfold MInv
      rcases hrel with hp | ⟨c, hp⟩ | hp
      · rw [hp] at hM hph
        obtain ⟨d0, hd0, _, hc, _⟩ := hph
        exact (hnodrop d0 (by rw [hp]; nofun) hd0 hc hM hdrop).elim
      · rw [hp] at hM hph
        obtain ⟨d0, hd0, _, ⟨hc, _⟩, _⟩ := hph
        exact (hnodrop d0 (by rw [hp]; nofun) hd0 hc hM hdrop).elim
      · rw [hp] at hM
        rw [hp]
        exact hM
    · unfold MInv
      rcases hrel with hp | ⟨c, hp⟩ | hp
      · rw [hp] at hM
        rw [hp]
        show (s.leaves2 ++ [h]) ++ rest = s.log1
        rw [← hM, hr]; simp
      · rw [hp] at hM
        rw [hp]
        show (s.leaves2 ++ [h]) ++ rest = s.log1
        rw [← hM, hr]; simp
      · rw [hp] at hM
        rw [hp]
        exact hM
  | gwPipeline info b =>
    obtain ⟨d, t, hd, hset, _, _, rfl⟩ := pm_stepGwPipeline hs
    unfold MInv
    cases hp : s.phase with
    | onL1 => trivial
    | toGW pre c => trivial
    | gwFailed pre => trivial
    | gwMinted pre => rw [hp] at hM; exact hM
    | onGW => rw [hp] at hM; exact hM
    | toL1 c => rw [hp] at hM; exact hM
    | back =>
      rw [hp] at hph
      obtain ⟨_, d0, hd0, hs2⟩ := hph
      rw [hd] at hd0; cases hd0
      rw [hs2] at hset; cases hset
  | gwPause ts =>
    obtain ⟨d, _, rfl⟩ := pm_stepGwPause hs
    exact hM
  | freezeGW =>
    obtain ⟨d, _, rfl⟩ := pm_stepFreezeGW hs
    exact hM
  | unfreezeGW =>
    obtain ⟨d, _, rfl⟩ := pm_stepUnfreezeGW hs
    exact hM
  | gwBurn =>
    obtain ⟨d, c, hp, _, _, _, _, _, rfl⟩ := pm_stepGwBurn hs
    rw [hp] at hM
    exact hM
  | l1Mint =>
    obtain ⟨c, b, t, hp, _, _, _, _, _, _, hre, rfl⟩ := pm_stepL1Mint hs
    obtain ⟨_, _, _, rfl⟩ := pm_l1Reinit hre
    rw [hp] at hM hph
    obtain ⟨d, _, _, ⟨_, he, _⟩, hco⟩ := hph
    have hpre : s.executed <+: s.log1 := by
      rw [he]; exact (List.take_prefix _ _).trans (by rw [← hM]; exact List.prefix_append _ _)
    show s.executed = s.log1.take c.priorityTree.unprocessedIndex
    rw [hco.2.2.1]
    exact List.prefix_iff_eq_take.mp hpre
  | tick dt =>
    cases hs
    exact hM

theorem pm_minv_reach {P : Params} {s : St} (h : Reach P Honest s) : GInv P s ∧ MInv s :=
  pm_steps_induct (I := fun s => GInv P s ∧ MInv s)
    (fun _ _ _ hI hok hst => ⟨pm_ginv_step hI.1 hok.1 hst, pm_minv_step hI.1 hI.2 hok hst⟩) h
    ⟨pm_ginv_initial P, trivial⟩

/-! ## The dropped relays in every reachable state -/

/-- The gateway leaves, the pending relays and the dropped relays account for the L1 leaves, and
with nothing dropped the gateway leaves followed by the pending relays are the L1 leaves. -/
def MirrorBook (s : St) : Prop :=
  s.leaves2.length + s.relays.length + s.dropped.length = s.log1.length
  ∧ (s.dropped = [] → s.leaves2 ++ s.relays = s.log1)

/-- Nothing is dropped before the gateway copy exists; `MirrorBook` from its creation until the
L1 mint. -/
def DInv (s : St) : Prop :=
  match s.phase with
  | .onL1 => s.dropped = []
  | .toGW _ _ => s.dropped = []
  | .gwFailed _ => s.dropped = []
  | .gwMinted _ => MirrorBook s
  | .onGW => MirrorBook s
  | .toL1 _ => MirrorBook s
  | .back => True

/-- A step that keeps the phase and the four lists keeps `DInv`. -/
theorem pm_dinv_frame {s s' : St} (hp : s'.phase = s.phase) (hl : s'.leaves2 = s.leaves2)
    (hr : s'.relays = s.relays) (hd : s'.dropped = s.dropped) (hlog : s'.log1 = s.log1)
    (h : DInv s) : DInv s' := by
  unfold DInv MirrorBook at h ⊢
  rw [hp, hl, hr, hd, hlog]
  exact h

/-- A relay step from a state with `MirrorBook` keeps it, whether it drops or pushes. -/
theorem pm_mirrorBook_relay {s : St} {h : UInt256} {rest : List UInt256} (hr : s.relays = h :: rest)
    (hB : MirrorBook s) :
    MirrorBook { s with relays := rest, dropped := s.dropped ++ [h] }
    ∧ ∀ d', MirrorBook { s with relays := rest, d2 := d', leaves2 := s.leaves2 ++ [h] } := by
  obtain ⟨hlen, hmir⟩ := hB
  rw [hr, List.length_cons] at hlen
  refine ⟨⟨?_, fun h0 => ?_⟩, fun d' => ⟨?_, fun h0 => ?_⟩⟩
  · show s.leaves2.length + rest.length + (s.dropped ++ [h]).length = s.log1.length
    rw [List.length_append, List.length_singleton]; omega
  · simp at h0
  · show (s.leaves2 ++ [h]).length + rest.length + s.dropped.length = s.log1.length
    rw [List.length_append, List.length_singleton]; omega
  · show (s.leaves2 ++ [h]) ++ rest = s.log1
    rw [← hmir h0, hr]; simp

theorem pm_dinv_step {P : Params} {s s' : St} {op : Op} (hS : SnapInv s) (hD : DInv s)
    (hs : step P s op = some s') : DInv s' := by
  have hsn := hS
  unfold SnapInv at hsn
  cases op with
  | request h =>
    obtain ⟨_, hpd, t, _, rfl⟩ := pm_stepRequest hs
    unfold DInv at hD ⊢
    cases hp : s.phase with
    | onL1 => rw [hp] at hD; exact hD
    | toGW pre c =>
      rw [hp] at hsn
      rw [pm_depositsPaused_of_inProgress hsn.1.1] at hpd; cases hpd
    | gwMinted pre =>
      rw [hp] at hsn
      rw [pm_depositsPaused_of_inProgress hsn.1.1] at hpd; cases hpd
    | gwFailed pre =>
      rw [hp] at hsn
      rw [pm_depositsPaused_of_inProgress hsn.1.1] at hpd; cases hpd
    | onGW =>
      rw [hp] at hD hsn
      obtain ⟨hlen, hmir⟩ := hD
      refine ⟨?_, fun h0 => ?_⟩
      · show s.leaves2.length + (if s.d1.settling then s.relays else s.relays ++ [h]).length
          + s.dropped.length = (s.log1 ++ [h]).length
        rw [hsn.1]
        simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton]
        omega
      · show s.leaves2 ++ (if s.d1.settling then s.relays else s.relays ++ [h]) = s.log1 ++ [h]
        rw [hsn.1, ← hmir h0]
        simp
    | toL1 c =>
      rw [hp] at hD hsn
      obtain ⟨hlen, hmir⟩ := hD
      refine ⟨?_, fun h0 => ?_⟩
      · show s.leaves2.length + (if s.d1.settling then s.relays else s.relays ++ [h]).length
          + s.dropped.length = (s.log1 ++ [h]).length
        rw [hsn.1]
        simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton]
        omega
      · show s.leaves2 ++ (if s.d1.settling then s.relays else s.relays ++ [h]) = s.log1 ++ [h]
        rw [hsn.1, ← hmir h0]
        simp
    | back => trivial
  | l1Pipeline info b =>
    obtain ⟨_, _, _, _, rfl⟩ := pm_stepL1Pipeline hs
    exact pm_dinv_frame rfl rfl rfl rfl rfl hD
  | pauseL1 =>
    obtain ⟨_, _, rfl⟩ := pm_stepPauseL1 hs
    exact pm_dinv_frame rfl rfl rfl rfl rfl hD
  | unpauseL1 =>
    obtain ⟨_, _, rfl⟩ := pm_stepUnpauseL1 hs
    exact pm_dinv_frame rfl rfl rfl rfl rfl hD
  | freezeL1 =>
    obtain rfl := pm_stepFreezeL1 hs
    exact pm_dinv_frame rfl rfl rfl rfl rfl hD
  | unfreezeL1 =>
    obtain rfl := pm_stepUnfreezeL1 hs
    exact pm_dinv_frame rfl rfl rfl rfl rfl hD
  | l1Burn =>
    obtain ⟨hp, _, _, _, _, c, _, rfl⟩ := pm_stepL1Burn hs
    unfold DInv at hD
    rw [hp] at hD
    exact hD
  | gwMint =>
    obtain ⟨pre, c, t, b, hp, _, _, _, _, rfl⟩ := pm_stepGwMint hs
    unfold DInv at hD
    rw [hp] at hD hsn
    have hd0 : s.dropped = [] := hD
    have hr0 : s.relays = [] := hsn.1.2.2.2.2.2.2.2
    refine ⟨?_, fun _ => ?_⟩
    · show s.log1.length + s.relays.length + s.dropped.length = s.log1.length
      rw [hr0, hd0]; rfl
    · show s.log1 ++ s.relays = s.log1
      rw [hr0, List.append_nil]
  | gwMintFails =>
    obtain ⟨pre, c, hp, rfl⟩ := pm_stepGwMintFails hs
    unfold DInv at hD
    rw [hp] at hD
    exact hD
  | confirm success =>
    rcases pm_stepConfirm hs with ⟨pre, hp, _, rfl⟩ | ⟨pre, hp, _, _, rfl⟩
    · unfold DInv at hD
      rw [hp] at hD
      exact hD
    · unfold DInv at hD
      rw [hp] at hD
      exact hD
  | relay =>
    obtain ⟨h, rest, hr, hcase⟩ := pm_stepRelay hs
    unfold DInv at hD
    rcases hcase with ⟨rfl, _⟩ | ⟨d, t, _, _, _, rfl⟩
    · unfold DInv
      cases hp : s.phase with
      | onL1 => rw [hp] at hsn; rw [hsn.2.2.2] at hr; cases hr
      | toGW pre c => rw [hp] at hsn; rw [hsn.1.2.2.2.2.2.2.2] at hr; cases hr
      | gwMinted pre => rw [hp] at hsn; rw [hsn.1.2.2.2.2.2.2.2] at hr; cases hr
      | gwFailed pre => rw [hp] at hsn; rw [hsn.1.2.2.2.2.2.2.2] at hr; cases hr
      | onGW => rw [hp] at hD; exact (pm_mirrorBook_relay hr hD).1
      | toL1 c => rw [hp] at hD; exact (pm_mirrorBook_relay hr hD).1
      | back => trivial
    · unfold DInv
      cases hp : s.phase with
      | onL1 => rw [hp] at hsn; rw [hsn.2.2.2] at hr; cases hr
      | toGW pre c => rw [hp] at hsn; rw [hsn.1.2.2.2.2.2.2.2] at hr; cases hr
      | gwMinted pre => rw [hp] at hsn; rw [hsn.1.2.2.2.2.2.2.2] at hr; cases hr
      | gwFailed pre => rw [hp] at hsn; rw [hsn.1.2.2.2.2.2.2.2] at hr; cases hr
      | onGW => rw [hp] at hD; exact (pm_mirrorBook_relay hr hD).2 (some { d with tree := t })
      | toL1 c => rw [hp] at hD; exact (pm_mirrorBook_relay hr hD).2 (some { d with tree := t })
      | back => trivial
  | gwPipeline info b =>
    obtain ⟨_, _, _, _, _, _, rfl⟩ := pm_stepGwPipeline hs
    exact pm_dinv_frame rfl rfl rfl rfl rfl hD
  | gwPause ts =>
    obtain ⟨_, _, rfl⟩ := pm_stepGwPause hs
    exact pm_dinv_frame rfl rfl rfl rfl rfl hD
  | freezeGW =>
    obtain ⟨_, _, rfl⟩ := pm_stepFreezeGW hs
    exact pm_dinv_frame rfl rfl rfl rfl rfl hD
  | unfreezeGW =>
    obtain ⟨_, _, rfl⟩ := pm_stepUnfreezeGW hs
    exact pm_dinv_frame rfl rfl rfl rfl rfl hD
  | gwBurn =>
    obtain ⟨d, c, hp, _, _, _, _, _, rfl⟩ := pm_stepGwBurn hs
    unfold DInv at hD
    rw [hp] at hD
    exact hD
  | l1Mint =>
    obtain ⟨c, b, t, hp, _, _, _, _, _, _, _, rfl⟩ := pm_stepL1Mint hs
    trivial
  | tick dt =>
    cases hs
    exact hD

theorem pm_dinv_reach {P : Params} {ok : St → Op → Prop} {s : St} (h : Reach P ok s) :
    SnapInv s ∧ DInv s :=
  pm_steps_induct (I := fun s => SnapInv s ∧ DInv s)
    (fun _ _ _ hI _ hst => ⟨pm_snapInv_step hI.1 hst, pm_dinv_step hI.1 hI.2 hst⟩) h
    ⟨pm_snapInv_initial P, rfl⟩

/-- `MirrorBook` turns the mirror equation into the absence of drops. -/
theorem pm_mirrorBook_iff {s : St} (hB : MirrorBook s) :
    s.leaves2 ++ s.relays = s.log1 ↔ s.dropped = [] := by
  refine ⟨fun hm => ?_, hB.2⟩
  have hlen := hB.1
  have hl : (s.leaves2 ++ s.relays).length = s.log1.length := by rw [hm]
  rw [List.length_append] at hl
  exact List.eq_nil_of_length_eq_zero (by omega)

/-- From the gateway copy's creation until the L1 mint, `MirrorBook` holds. -/
theorem pm_dinv_mirrored {s : St} (hD : DInv s) (hm : s.phase.Mirrored) : MirrorBook s := by
  unfold DInv at hD
  unfold Phase.Mirrored at hm
  cases hp : s.phase with
  | gwMinted pre => rw [hp] at hD; exact hD
  | onGW => rw [hp] at hD; exact hD
  | toL1 c => rw [hp] at hD; exact hD
  | onL1 => rw [hp] at hm; exact hm.elim
  | toGW pre c => rw [hp] at hm; exact hm.elim
  | gwFailed pre => rw [hp] at hm; exact hm.elim
  | back => rw [hp] at hm; exact hm.elim

/-- A push of the next relay into a gateway copy that holds its leaves succeeds, if the L1 tree
holds at least one more leaf. -/
theorem pm_gw_write_succeeds {P : Params} {s : St} {d : ChainDiamond} {h : UInt256}
    (hI : GInv P s) (hc : Copy2 P s d) (hlen : s.leaves2.length + 1 ≤ s.log1.length) :
    ∃ t, mailboxWrite P.tree d.tree h = some t := by
  obtain ⟨⟨_, hpos, _⟩, hn⟩ := pm_pushAll_setup hc.2
  have hne : s.log1 ≠ [] := by
    intro hnil; rw [hnil, List.length_nil] at hlen; omega
  have hb := hI.bound1 hne
  have hpush : ∃ tree r, d.tree.tree.push P.tree.node h = some (tree, r) := by
    unfold PushTree.push
    split
    · omega
    · split
      · omega
      · exact ⟨_, _, rfl⟩
  obtain ⟨tree, r, hp⟩ := hpush
  have htn := (pm_push_shape (pm_pushAll_setup hc.2).1 hp).2.2
  exact ⟨_, pm_mailboxWrite_of_push hp (by rw [hc.1, htn, hn]; omega)⟩

/-! ## Each step only extends the two logs -/

theorem pm_step_logs {P : Params} {s s' : St} {op : Op} (hs : step P s op = some s') :
    s.executed <+: s'.executed ∧ s.log1 <+: s'.log1 := by
  cases op with
  | request h =>
    obtain ⟨_, _, _, _, rfl⟩ := pm_stepRequest hs
    exact ⟨List.prefix_refl _, List.prefix_append _ _⟩
  | l1Pipeline info b =>
    obtain ⟨_, _, _, _, rfl⟩ := pm_stepL1Pipeline hs
    exact ⟨List.prefix_append _ _, List.prefix_refl _⟩
  | pauseL1 =>
    obtain ⟨_, _, rfl⟩ := pm_stepPauseL1 hs
    exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  | unpauseL1 =>
    obtain ⟨_, _, rfl⟩ := pm_stepUnpauseL1 hs
    exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  | freezeL1 =>
    obtain rfl := pm_stepFreezeL1 hs
    exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  | unfreezeL1 =>
    obtain rfl := pm_stepUnfreezeL1 hs
    exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  | l1Burn =>
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := pm_stepL1Burn hs
    exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  | gwMint =>
    obtain ⟨_, _, _, _, _, _, _, _, _, rfl⟩ := pm_stepGwMint hs
    exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  | gwMintFails =>
    obtain ⟨_, _, _, rfl⟩ := pm_stepGwMintFails hs
    exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  | confirm success =>
    rcases pm_stepConfirm hs with ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩
    · exact ⟨List.prefix_refl _, List.prefix_refl _⟩
    · exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  | relay =>
    obtain ⟨_, _, _, hc⟩ := pm_stepRelay hs
    rcases hc with ⟨rfl, _⟩ | ⟨_, _, _, _, _, rfl⟩
    · exact ⟨List.prefix_refl _, List.prefix_refl _⟩
    · exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  | gwPipeline info b =>
    obtain ⟨_, _, _, _, _, _, rfl⟩ := pm_stepGwPipeline hs
    exact ⟨List.prefix_append _ _, List.prefix_refl _⟩
  | gwPause ts =>
    obtain ⟨_, _, rfl⟩ := pm_stepGwPause hs
    exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  | freezeGW =>
    obtain ⟨_, _, rfl⟩ := pm_stepFreezeGW hs
    exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  | unfreezeGW =>
    obtain ⟨_, _, rfl⟩ := pm_stepUnfreezeGW hs
    exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  | gwBurn =>
    obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := pm_stepGwBurn hs
    exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  | l1Mint =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := pm_stepL1Mint hs
    exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  | tick dt =>
    cases hs
    exact ⟨List.prefix_refl _, List.prefix_refl _⟩

theorem pm_steps_logs {P : Params} {ok : St → Op → Prop} {s t : St} (h : Steps P ok s t) :
    s.executed <+: t.executed ∧ s.log1 <+: t.log1 := by
  induction h with
  | refl => exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  | tail op _ _ hst ih =>
    obtain ⟨h1, h2⟩ := pm_step_logs hst
    exact ⟨ih.1.trans h1, ih.2.trans h2⟩

/-- Each step only extends the list of dropped relays. -/
theorem pm_step_dropped {P : Params} {s s' : St} {op : Op} (hs : step P s op = some s') :
    s.dropped <+: s'.dropped := by
  cases op with
  | request h => obtain ⟨_, _, _, _, rfl⟩ := pm_stepRequest hs; exact List.prefix_refl _
  | l1Pipeline info b => obtain ⟨_, _, _, _, rfl⟩ := pm_stepL1Pipeline hs; exact List.prefix_refl _
  | pauseL1 => obtain ⟨_, _, rfl⟩ := pm_stepPauseL1 hs; exact List.prefix_refl _
  | unpauseL1 => obtain ⟨_, _, rfl⟩ := pm_stepUnpauseL1 hs; exact List.prefix_refl _
  | freezeL1 => obtain rfl := pm_stepFreezeL1 hs; exact List.prefix_refl _
  | unfreezeL1 => obtain rfl := pm_stepUnfreezeL1 hs; exact List.prefix_refl _
  | l1Burn => obtain ⟨_, _, _, _, _, _, _, rfl⟩ := pm_stepL1Burn hs; exact List.prefix_refl _
  | gwMint => obtain ⟨_, _, _, _, _, _, _, _, _, rfl⟩ := pm_stepGwMint hs; exact List.prefix_refl _
  | gwMintFails => obtain ⟨_, _, _, rfl⟩ := pm_stepGwMintFails hs; exact List.prefix_refl _
  | confirm success =>
    rcases pm_stepConfirm hs with ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩
    · exact List.prefix_refl _
    · exact List.prefix_refl _
  | relay =>
    obtain ⟨_, _, _, hc⟩ := pm_stepRelay hs
    rcases hc with ⟨rfl, _⟩ | ⟨_, _, _, _, _, rfl⟩
    · exact List.prefix_append _ _
    · exact List.prefix_refl _
  | gwPipeline info b =>
    obtain ⟨_, _, _, _, _, _, rfl⟩ := pm_stepGwPipeline hs; exact List.prefix_refl _
  | gwPause ts => obtain ⟨_, _, rfl⟩ := pm_stepGwPause hs; exact List.prefix_refl _
  | freezeGW => obtain ⟨_, _, rfl⟩ := pm_stepFreezeGW hs; exact List.prefix_refl _
  | unfreezeGW => obtain ⟨_, _, rfl⟩ := pm_stepUnfreezeGW hs; exact List.prefix_refl _
  | gwBurn => obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := pm_stepGwBurn hs; exact List.prefix_refl _
  | l1Mint =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := pm_stepL1Mint hs; exact List.prefix_refl _
  | tick dt => cases hs; exact List.prefix_refl _

theorem pm_steps_dropped {P : Params} {ok : St → Op → Prop} {s t : St} (h : Steps P ok s t) :
    s.dropped <+: t.dropped := by
  induction h with
  | refl => exact List.prefix_refl _
  | tail op _ _ hst ih => exact ih.trans (pm_step_dropped hst)

/-- With migrations disabled, the phase stays `onL1`. -/
theorem pm_onL1_step {P : Params} {s s' : St} {op : Op} (hdis : P.migrationsEnabled = false)
    (hI : s.phase = .onL1) (hs : step P s op = some s') : s'.phase = .onL1 := by
  cases op with
  | request h => obtain ⟨_, _, _, _, rfl⟩ := pm_stepRequest hs; exact hI
  | l1Pipeline info b => obtain ⟨_, _, _, _, rfl⟩ := pm_stepL1Pipeline hs; exact hI
  | pauseL1 => obtain ⟨_, _, rfl⟩ := pm_stepPauseL1 hs; exact hI
  | unpauseL1 => obtain ⟨_, _, rfl⟩ := pm_stepUnpauseL1 hs; exact hI
  | freezeL1 => obtain rfl := pm_stepFreezeL1 hs; exact hI
  | unfreezeL1 => obtain rfl := pm_stepUnfreezeL1 hs; exact hI
  | l1Burn => obtain ⟨_, hen, _⟩ := pm_stepL1Burn hs; rw [hdis] at hen; cases hen
  | gwMint => obtain ⟨_, _, _, _, hp, _⟩ := pm_stepGwMint hs; rw [hI] at hp; cases hp
  | gwMintFails => obtain ⟨_, _, hp, _⟩ := pm_stepGwMintFails hs; rw [hI] at hp; cases hp
  | confirm b =>
    rcases pm_stepConfirm hs with ⟨_, hp, _⟩ | ⟨_, hp, _⟩
    · rw [hI] at hp; cases hp
    · rw [hI] at hp; cases hp
  | relay =>
    obtain ⟨_, _, _, hc⟩ := pm_stepRelay hs
    rcases hc with ⟨rfl, _⟩ | ⟨_, _, _, _, _, rfl⟩
    · exact hI
    · exact hI
  | gwPipeline info b => obtain ⟨_, _, _, _, _, _, rfl⟩ := pm_stepGwPipeline hs; exact hI
  | gwPause ts => obtain ⟨_, _, rfl⟩ := pm_stepGwPause hs; exact hI
  | freezeGW => obtain ⟨_, _, rfl⟩ := pm_stepFreezeGW hs; exact hI
  | unfreezeGW => obtain ⟨_, _, rfl⟩ := pm_stepUnfreezeGW hs; exact hI
  | gwBurn => obtain ⟨_, _, hp, _⟩ := pm_stepGwBurn hs; rw [hI] at hp; cases hp
  | l1Mint => obtain ⟨_, _, _, hp, _⟩ := pm_stepL1Mint hs; rw [hI] at hp; cases hp
  | tick dt => cases hs; exact hI

theorem pm_request_blocked {P : Params} {s : St} {h : UInt256} (hp : depositsPausedL1 P s = true) :
    step P s (.request h) = none := by
  show stepRequest P s h = none
  unfold stepRequest
  split
  · rename_i hg; rw [hp] at hg; cases hg.2
  · rfl

/-! ## The L1 copy during the move to the gateway -/

theorem InProgressIffInFlight : Properties.InProgressIffInFlight :=
  fun _ _ h => pm_snap_inProgress (pm_snapInv_reach h)

theorem L1SnapshotFrozen : Properties.L1SnapshotFrozen := by
  intro P s pre h hpre
  have hI := pm_snapInv_reach h
  have hf : s.phase.InFlight := by unfold Phase.InFlight; rw [hpre]; rfl
  obtain ⟨pre', hpre', hfl⟩ := pm_snap_flight hI hf
  rw [hpre] at hpre'
  cases hpre'
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hfl
  have hdp := pm_depositsPaused_of_inProgress (P := P) h1
  refine ⟨h1, hdp, h3, h7, h2, h4, h5, h6, h8, fun x => pm_request_blocked hdp, ?_⟩
  intro c hc
  unfold SnapInv at hI
  rw [hc] at hI
  exact hI.2.2

theorem FailureRestoresL1 : Properties.FailureRestoresL1 := by
  intro P s s' h hs
  have hI := pm_snapInv_reach h
  rcases pm_stepConfirm hs with ⟨pre, _, hsu, _⟩ | ⟨pre, hp, _, _, rfl⟩
  · cases hsu
  · unfold SnapInv at hI
    rw [hp] at hI
    obtain ⟨⟨_, _, h3, h4, h5, _, _, _⟩, _⟩ := hI
    refine ⟨pre, hp, rfl, rfl, ?_⟩
    show ({ tree := s.d1.tree, settling := true, pausedTs := 0, frozen := s.d1.frozen,
            batches := s.d1.batches } : ChainDiamond)
      = { tree := pre.tree, settling := pre.settling, pausedTs := 0, frozen := s.d1.frozen,
          batches := pre.batches }
    rw [h3, h4, h5]

/-! ## The mirror -/

theorem MirrorPrefix : Properties.MirrorPrefix := by
  intro P s h hm
  obtain ⟨hG, hM⟩ := pm_minv_reach h
  have hph := hG.phase
  unfold GPhase at hph
  unfold MInv at hM
  unfold Phase.Mirrored at hm
  cases hp : s.phase with
  | gwMinted pre =>
    rw [hp] at hph hM
    obtain ⟨_, _, d, hd, hc, _, _, _⟩ := hph
    exact ⟨d, hd, by rw [hc.1, hG.start1], hM, hc.2, hG.tree1⟩
  | onGW =>
    rw [hp] at hph hM
    obtain ⟨d, hd, _, hc, _⟩ := hph
    exact ⟨d, hd, by rw [hc.1, hG.start1], hM, hc.2, hG.tree1⟩
  | toL1 c =>
    rw [hp] at hph hM
    obtain ⟨d, hd, _, ⟨hc, _⟩, _⟩ := hph
    exact ⟨d, hd, by rw [hc.1, hG.start1], hM, hc.2, hG.tree1⟩
  | onL1 => rw [hp] at hm; exact hm.elim
  | toGW pre c => rw [hp] at hm; exact hm.elim
  | gwFailed pre => rw [hp] at hm; exact hm.elim
  | back => rw [hp] at hm; exact hm.elim

theorem NoRelayDroppedBeforeReturn : Properties.NoRelayDroppedBeforeReturn := by
  intro P s h hnb
  obtain ⟨_, hM⟩ := pm_minv_reach h
  obtain ⟨_, hD⟩ := pm_dinv_reach h
  have hD' := hD
  unfold DInv at hD
  unfold MInv at hM
  cases hp : s.phase with
  | onL1 => rw [hp] at hD; exact hD
  | toGW pre c => rw [hp] at hD; exact hD
  | gwFailed pre => rw [hp] at hD; exact hD
  | gwMinted pre =>
    rw [hp] at hM
    exact (pm_mirrorBook_iff (pm_dinv_mirrored hD' (by rw [hp]; trivial))).mp hM
  | onGW =>
    rw [hp] at hM
    exact (pm_mirrorBook_iff (pm_dinv_mirrored hD' (by rw [hp]; trivial))).mp hM
  | toL1 c =>
    rw [hp] at hM
    exact (pm_mirrorBook_iff (pm_dinv_mirrored hD' (by rw [hp]; trivial))).mp hM
  | back => exact absurd hp hnb

/-! ## Relays, without FREEZE-ORDER -/

theorem RelayDropsIffFrozen : Properties.RelayDropsIffFrozen := by
  intro P s h rest hreach hnb hr
  have hG := pm_ginv_reach hreach
  have hsn := hG.snap
  have hph := hG.phase
  unfold SnapInv at hsn
  unfold GPhase at hph
  have key : ∃ d, s.d2 = some d ∧ Copy2 P s d
      ∧ s.leaves2.length + s.relays.length ≤ s.log1.length := by
    cases hp : s.phase with
    | onL1 => rw [hp] at hsn; rw [hsn.2.2.2] at hr; cases hr
    | toGW pre c => rw [hp] at hsn; rw [hsn.1.2.2.2.2.2.2.2] at hr; cases hr
    | gwMinted pre => rw [hp] at hsn; rw [hsn.1.2.2.2.2.2.2.2] at hr; cases hr
    | gwFailed pre => rw [hp] at hsn; rw [hsn.1.2.2.2.2.2.2.2] at hr; cases hr
    | onGW =>
      rw [hp] at hph
      obtain ⟨d, hd, _, hc, _, _, _, _, hrl⟩ := hph
      exact ⟨d, hd, hc, hrl⟩
    | toL1 c =>
      rw [hp] at hph
      obtain ⟨d, hd, _, ⟨hc, _, _, _, _, hrl⟩, _⟩ := hph
      exact ⟨d, hd, hc, hrl⟩
    | back => exact absurd hp hnb
  obtain ⟨d, hd, hc, hrl⟩ := key
  refine ⟨d, hd, fun hf => ?_, fun hf => ?_⟩
  · show stepRelay P s = some _
    simp [stepRelay, hr, hd, hf]
  · rw [hr, List.length_cons] at hrl
    obtain ⟨t, ht⟩ := pm_gw_write_succeeds hG hc (h := h) (by omega)
    refine ⟨t, ht, ?_⟩
    show stepRelay P s = some _
    simp [stepRelay, hr, hd, hf, ht]

theorem MirrorIffNoDrop : Properties.MirrorIffNoDrop := by
  intro P s h hm
  have hB := pm_dinv_mirrored (pm_dinv_reach h).2 hm
  exact ⟨hB.1, pm_mirrorBook_iff hB⟩

theorem MirrorBreakPermanent : Properties.MirrorBreakPermanent := by
  intro P s s' h hst hne hm' hmir
  have hreach' : Reach P Unrestricted s' := pm_steps_trans h hst
  have hd' : s'.dropped = [] := (MirrorIffNoDrop P s' hreach' hm').2.mp hmir
  obtain ⟨u, hu⟩ := pm_steps_dropped hst
  rw [hd'] at hu
  exact hne (List.append_eq_nil_iff.mp hu).1

/-! ## No operation lost or repeated -/

theorem ExecutedIsL1Prefix : Properties.ExecutedIsL1Prefix := by
  intro P s h
  obtain ⟨hG, hM⟩ := pm_minv_reach h
  have hsn := hG.snap
  have hph := hG.phase
  unfold SnapInv at hsn
  unfold GPhase at hph
  unfold MInv at hM
  cases hp : s.phase with
  | onL1 =>
    rw [hp] at hph
    exact ⟨by rw [hph]; exact List.take_prefix _ _, fun _ => ⟨hph, hG.u1⟩⟩
  | toGW pre c =>
    rw [hp] at hph hsn
    exact ⟨by rw [hph.1],
      fun hset => absurd (hsn.1.2.1.symm.trans hset) Bool.false_ne_true⟩
  | gwFailed pre =>
    rw [hp] at hph hsn
    exact ⟨by rw [hph.1],
      fun hset => absurd (hsn.1.2.1.symm.trans hset) Bool.false_ne_true⟩
  | gwMinted pre =>
    rw [hp] at hph hsn
    exact ⟨by rw [hph.1],
      fun hset => absurd (hsn.1.2.1.symm.trans hset) Bool.false_ne_true⟩
  | onGW =>
    rw [hp] at hph hsn hM
    obtain ⟨d, _, _, _, he, _⟩ := hph
    exact ⟨by
        rw [he]
        exact (List.take_prefix _ _).trans (by rw [← hM]; exact List.prefix_append _ _),
      fun hset => by rw [hsn.1] at hset; cases hset⟩
  | toL1 c =>
    rw [hp] at hph hsn hM
    obtain ⟨d, _, _, ⟨_, he, _⟩, _⟩ := hph
    exact ⟨by
        rw [he]
        exact (List.take_prefix _ _).trans (by rw [← hM]; exact List.prefix_append _ _),
      fun hset => by rw [hsn.1] at hset; cases hset⟩
  | back =>
    rw [hp] at hM
    exact ⟨by rw [hM]; exact List.take_prefix _ _, fun _ => ⟨hM, hG.u1⟩⟩

theorem ReturnMintPassesOnPrefix : Properties.ReturnMintPassesOnPrefix := by
  intro P s c h hp hen hpause hpre
  have hG := pm_ginv_reach h
  have hph := hG.phase
  have hsn := hG.snap
  unfold GPhase at hph
  unfold SnapInv at hsn
  rw [hp] at hph hsn
  obtain ⟨d, _, _, ⟨_, he, hdu, h1u, _, _⟩, hco⟩ := hph
  obtain ⟨hcs, hcn, hcu, ⟨zs, hzs⟩, hb1, hb2, hb3⟩ := hco
  have hexl : s.executed.length = d.tree.unprocessedIndex := by
    rw [he, List.length_take]; omega
  obtain ⟨⟨hsl, hzpos, _⟩, _⟩ := pm_pushAll_setup hzs
  have hsl' : c.priorityTree.sides.length = zs.length := hsl
  have hzpos' : 0 < zs.length := hzpos
  have hsides : c.priorityTree.sides ≠ [] := by
    intro hnil
    rw [hnil, List.length_nil] at hsl'
    omega
  have hroot : rootAfter P.tree s.executed = some (lastSide c.priorityTree) := by
    rw [pm_rootAfter_of_pushAll hzs]; rfl
  have hhist : s.d1.tree.isHistoricalRoot (lastSide c.priorityTree) = true :=
    (hG.hist1 _).mpr ⟨s.executed, hpre, hroot⟩
  have hre : (s.d1.tree.l1Reinit c.priorityTree).isSome = true :=
    pm_l1Reinit_isSome (by rw [hG.start1, hcs]) (by rw [hcu, hexl]; exact h1u)
      (by rw [hcn, pm_tree1_length hG]; exact hpre.length_le)
  have hmb : (mintBatches s.d1.batches c).isSome = true := by
    unfold mintBatches
    split
    · rfl
    · rename_i hn; exact absurd ⟨hb1, hb2, hb3⟩ hn
  refine ⟨hsides, hhist, hre, hmb, ?_⟩
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hre
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hmb
  have ht' := ht
  obtain ⟨_, _, _, rfl⟩ := pm_l1Reinit ht'
  refine ⟨{ s with
      d1 := { s.d1 with
        tree := { s.d1.tree with unprocessedIndex := c.priorityTree.unprocessedIndex },
        batches := b, settling := true, pausedTs := 0 }
      phase := .back }, ?_, rfl, ?_, ?_⟩
  · show stepL1Mint P s = some _
    unfold stepL1Mint
    split
    · rename_i c' hp'
      rw [hp] at hp'
      cases hp'
      split
      · rw [hb, ht]
      · rename_i hn
        exact absurd ⟨hen, hpause, hsides, hhist, hsn.1⟩ hn
    · rename_i hn
      exact absurd hp (hn c)
  · show c.priorityTree.unprocessedIndex = s.executed.length
    exact hcu
  · show s.executed = s.log1.take c.priorityTree.unprocessedIndex
    rw [hcu]
    exact List.prefix_iff_eq_take.mp hpre

theorem ReturnMintChecksPass : Properties.ReturnMintChecksPass :=
  fun P s c h hp hen hpause =>
    ReturnMintPassesOnPrefix P s c (pm_steps_mono (fun _ _ hok => hok.1) h) hp hen hpause
      (ExecutedIsL1Prefix P s h).1

/-! ## Without FREEZE-ORDER -/

theorem ReturnRootCheckIffRootMatch : Properties.ReturnRootCheckIffRootMatch := by
  intro P s c h hp
  have hG := pm_ginv_reach h
  have hph := hG.phase
  unfold GPhase at hph
  rw [hp] at hph
  obtain ⟨_, _, _, _, hco⟩ := hph
  obtain ⟨_, _, _, ⟨zs, hzs⟩, _⟩ := hco
  have hroot : rootAfter P.tree s.executed = some (lastSide c.priorityTree) := by
    rw [pm_rootAfter_of_pushAll hzs]; rfl
  refine ⟨hroot, ?_⟩
  rw [hroot]
  exact hG.hist1 _

theorem BrokenReturnNeedsRootCollision : Properties.BrokenReturnNeedsRootCollision := by
  intro P s c h hp hn hh
  obtain ⟨_, hiff⟩ := ReturnRootCheckIffRootMatch P s c h hp
  obtain ⟨p, hp', hr⟩ := hiff.mp hh
  exact ⟨p, hp', fun he => hn (he ▸ hp'), hr⟩

theorem ExecutedDivergencePermanent : Properties.ExecutedDivergencePermanent := by
  intro P s s' h hst hn h'
  have hlen := (pm_ginv_reach h).execLen
  obtain ⟨hE, hL⟩ := pm_steps_logs hst
  exact hn (List.prefix_of_prefix_length_le (hE.trans h') hL hlen)

/-! ## At this commit -/

theorem MigrationsDisabledKeepL1Settling : Properties.MigrationsDisabledKeepL1Settling := by
  intro P s hdis h
  have key : s.phase = .onL1 :=
    pm_steps_induct (I := fun s => s.phase = .onL1)
      (fun _ _ _ hI _ hst => pm_onL1_step hdis hI hst) h rfl
  have hsn := pm_snapInv_reach h
  unfold SnapInv at hsn
  rw [key] at hsn
  exact ⟨key, hsn.1, hsn.2.1, hsn.2.2.1, hsn.2.2.2⟩

/-! ## Concrete runs -/

/-- `ConsistentProcessing`, decided. -/
def consistentB (s : St) : Op → Bool
  | .l1Pipeline info _ =>
      decide (s.d1.tree.unprocessedIndex + info.itemHashes.length ≤ s.d1.tree.tree.nextLeafIndex)
  | .gwPipeline info _ =>
      match s.d2 with
      | none => true
      | some d =>
          decide (d.tree.unprocessedIndex + info.itemHashes.length ≤ d.tree.tree.nextLeafIndex)
  | _ => true

/-- `FreezeOrder`, decided. -/
def freezeOrderB (s : St) : Op → Bool
  | .relay =>
      match s.phase with
      | .back => true
      | _ =>
          match s.d2 with
          | none => true
          | some d => !d.frozen
  | _ => true

/-- `Honest`, decided. -/
def honestB (s : St) (op : Op) : Bool := consistentB s op && freezeOrderB s op

theorem pm_consistentB {s : St} {op : Op} (h : consistentB s op = true) :
    ConsistentProcessing s op := by
  cases op
  case l1Pipeline info b => simpa [consistentB, ConsistentProcessing] using h
  case gwPipeline info b =>
    intro d hd
    simp only [consistentB, hd, decide_eq_true_eq] at h
    exact h
  all_goals trivial

theorem pm_freezeOrderB {s : St} {op : Op} (h : freezeOrderB s op = true) : FreezeOrder s op := by
  cases op
  case relay =>
    show s.phase = .back ∨ ∀ d, s.d2 = some d → d.frozen = false
    cases hp : s.phase with
    | back => exact Or.inl rfl
    | onL1 | toGW _ _ | gwMinted _ | gwFailed _ | onGW | toL1 _ =>
      refine Or.inr fun d hd => ?_
      simp only [freezeOrderB, hp, hd, Bool.not_eq_true'] at h
      exact h
  all_goals trivial

theorem pm_honestB {s : St} {op : Op} (h : honestB s op = true) : Honest s op := by
  unfold honestB at h
  rw [Bool.and_eq_true] at h
  exact ⟨pm_consistentB h.1, pm_freezeOrderB h.2⟩

/-- Run `ops` from `s`, checking `okB` before each step. -/
def runChecked (P : Params) (okB : St → Op → Bool) : St → List Op → Option St
  | s, [] => some s
  | s, op :: ops =>
      if okB s op then
        match step P s op with
        | none => none
        | some s' => runChecked P okB s' ops
      else none

theorem pm_runChecked_steps {P : Params} {okB : St → Op → Bool} {ok : St → Op → Prop}
    (hok : ∀ s op, okB s op = true → ok s op) :
    ∀ {s t : St} {ops : List Op}, runChecked P okB s ops = some t → Steps P ok s t
  | s, t, [], h => by cases h; exact Steps.refl s
  | s, t, op :: ops, h => by
    unfold runChecked at h
    split at h
    · rename_i hb
      split at h
      · cases h
      · rename_i s' hs'
        exact pm_steps_head (hok _ _ hb) hs' (pm_runChecked_steps hok h)
    · cases h

theorem pm_runChecked_append {P : Params} {okB : St → Op → Bool} (s : St) (ops₁ ops₂ : List Op) :
    runChecked P okB s (ops₁ ++ ops₂) =
      (runChecked P okB s ops₁).bind (fun t => runChecked P okB t ops₂) := by
  induction ops₁ generalizing s with
  | nil => rfl
  | cons op ops ih =>
    rw [List.cons_append, runChecked.eq_2, runChecked.eq_2]
    by_cases hb : okB s op = true
    · simp only [hb, ↓reduceIte]
      cases step P s op with
      | none => rfl
      | some s' => exact ih s'
    · simp [hb]

theorem pm_run_split {P : Params} {okB : St → Op → Bool} {s₀ : St} {ops₁ ops₂ : List Op}
    (h₀ : runChecked P okB (initial P) ops₁ = some s₀) :
    runChecked P okB (initial P) (ops₁ ++ ops₂) = runChecked P okB s₀ ops₂ := by
  rw [pm_runChecked_append, h₀]
  rfl

theorem pm_run_proj {α : Type} (f : St → α) {r : Option St} {t : St} {v : α}
    (hr : r = some t) (hv : r.map f = some v) : f t = v := by
  rw [hr] at hv
  exact Option.some.inj hv

/-- The commitment of an in-flight return, if any. -/
def toL1Commit : Phase → Option ChainCommitment
  | .toL1 c => some c
  | _ => none

theorem pm_toL1Commit {p : Phase} {c : ChainCommitment} (h : toL1Commit p = some c) :
    p = .toL1 c := by
  cases p <;> simp only [toL1Commit, reduceCtorEq] at h
  cases h
  rfl

/-- A tag per phase, for reading phases off concrete runs. -/
def phaseTag : Phase → ℕ
  | .onL1 => 0
  | .toGW _ _ => 1
  | .gwMinted _ => 2
  | .gwFailed _ => 3
  | .onGW => 4
  | .toL1 _ => 5
  | .back => 6

theorem pm_phaseTag_onGW {p : Phase} (h : phaseTag p = 4) : p = .onGW := by
  cases p <;> simp_all [phaseTag]

theorem pm_phaseTag_back {p : Phase} (h : phaseTag p = 6) : p = .back := by
  cases p <;> simp_all [phaseTag]


/-- An in-flight return: its commitment. -/
theorem pm_run_toL1 {r : Option St} {s : St} (hr : r = some s)
    (hv : r.map (fun s => (toL1Commit s.phase).isSome) = some true) :
    ∃ c, s.phase = .toL1 c ∧ toL1Commit s.phase = some c := by
  have h := pm_run_proj (fun s => (toL1Commit s.phase).isSome) hr hv
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
  exact ⟨c, pm_toL1Commit hc, hc⟩

theorem pm_run_toL1_proj {α : Type} (f : St → ChainCommitment → α) {r : Option St} {s : St}
    {c : ChainCommitment} {v : α} (hr : r = some s) (hc : toL1Commit s.phase = some c)
    (hv : r.map (fun s => (toL1Commit s.phase).map (f s)) = some (some v)) : f s c = v := by
  have h := pm_run_proj (fun s => (toL1Commit s.phase).map (f s)) hr hv
  simp only [hc, Option.map_some] at h
  exact Option.some.inj h

/-! ## Witnesses -/

theorem InProgressIffInFlightWitness : Properties.InProgressIffInFlightWitness := by
  obtain ⟨s, h⟩ := Option.isSome_iff_exists.mp
    (show (runChecked wParams (fun _ _ => true) (initial wParams) (honestRun.take 5)).isSome = true by
      decide)
  obtain ⟨s', h'⟩ := Option.isSome_iff_exists.mp
    (show (runChecked wParams (fun _ _ => true) (initial wParams) (honestRun.take 7)).isSome = true by
      decide)
  have e1 : s.inProgress = true := pm_run_proj St.inProgress h (by decide)
  have e2 : s.phase.preBurn.isSome = true :=
    pm_run_proj (fun s => s.phase.preBurn.isSome) h (by decide)
  have e3 : s'.inProgress = false := pm_run_proj St.inProgress h' (by decide)
  have e4 : phaseTag s'.phase = 4 := pm_run_proj (fun s => phaseTag s.phase) h' (by decide)
  exact ⟨s, s', pm_runChecked_steps (fun _ _ _ => trivial) h, e1, e2,
    pm_runChecked_steps (fun _ _ _ => trivial) h', e3, pm_phaseTag_onGW e4⟩

theorem L1SnapshotFrozenWitness : Properties.L1SnapshotFrozenWitness := by
  obtain ⟨s, h⟩ := Option.isSome_iff_exists.mp
    (show (runChecked wParams (fun _ _ => true) (initial wParams) failedRun).isSome = true by decide)
  have e1 : s.phase.preBurn.map (fun pre =>
      (pre.tree.tree.nextLeafIndex, pre.tree.unprocessedIndex, pre.frozen)) = some (1, 1, false) :=
    pm_run_proj (fun s => s.phase.preBurn.map (fun pre =>
      (pre.tree.tree.nextLeafIndex, pre.tree.unprocessedIndex, pre.frozen))) h (by decide)
  have e2 : s.d1.frozen = true := pm_run_proj (fun s => s.d1.frozen) h (by decide)
  cases hp : s.phase.preBurn with
  | none => rw [hp] at e1; cases e1
  | some pre =>
    rw [hp] at e1
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e1
    exact ⟨s, pre, pm_runChecked_steps (fun _ _ _ => trivial) h, hp, e1.1, e1.2.1, e1.2.2, e2⟩

theorem FailureRestoresL1Witness : Properties.FailureRestoresL1Witness := by
  obtain ⟨s, h⟩ := Option.isSome_iff_exists.mp
    (show (runChecked wParams (fun _ _ => true) (initial wParams) failedRun).isSome = true by decide)
  have e0 : (step wParams s (.confirm false)).map
      (fun s' => (s'.d1.settling, s'.d1.tree.tree.nextLeafIndex, s'.d1.tree.unprocessedIndex))
      = some (true, 1, 1) :=
    pm_run_proj (fun s => (step wParams s (.confirm false)).map
      (fun s' => (s'.d1.settling, s'.d1.tree.tree.nextLeafIndex, s'.d1.tree.unprocessedIndex))) h
      (by decide)
  have e1 : (s.d1.pausedTs != 0) = true := pm_run_proj (fun s => s.d1.pausedTs != 0) h (by decide)
  cases hs : step wParams s (.confirm false) with
  | none => rw [hs] at e0; cases e0
  | some s' =>
    rw [hs] at e0
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e0
    refine ⟨s, s', pm_runChecked_steps (fun _ _ _ => trivial) h, hs, ?_, e0.1, e0.2.1, e0.2.2⟩
    simpa using e1

theorem MirrorPrefixWitness : Properties.MirrorPrefixWitness := by
  obtain ⟨s₀, h₀⟩ := Option.isSome_iff_exists.mp
    (show (runChecked wParams honestB (initial wParams) (honestRun.take 9)).isSome = true by decide)
  have hall : (runChecked wParams honestB (initial wParams)
      (honestRun.take 9 ++ honestRun.drop 9)).isSome = true := by
    rw [List.take_append_drop]; decide
  rw [pm_run_split h₀] at hall
  obtain ⟨s, h₁⟩ := Option.isSome_iff_exists.mp hall
  have hfull : runChecked wParams honestB (initial wParams) honestRun = some s := by
    rw [← List.take_append_drop 9 honestRun, pm_run_split h₀]; exact h₁
  have hd2 : s₀.d2.map ChainDiamond.frozen = some true :=
    pm_run_proj (fun s => s.d2.map ChainDiamond.frozen) h₀ (by decide)
  have hrel₀ : s₀.relays = [1] := pm_run_proj St.relays h₀ (by decide)
  obtain ⟨c, hp, _⟩ := pm_run_toL1 hfull (by decide)
  have e1 : s.leaves2 = [11, 1, 2] := pm_run_proj St.leaves2 hfull (by decide)
  have e2 : s.relays = [3] := pm_run_proj St.relays hfull (by decide)
  have e3 : s.log1 = [11, 1, 2, 3] := pm_run_proj St.log1 hfull (by decide)
  cases hd : s₀.d2 with
  | none => rw [hd] at hd2; cases hd2
  | some d =>
    rw [hd] at hd2
    refine ⟨s₀, s, d, pm_runChecked_steps (fun _ _ h => pm_honestB h) h₀, hd,
      Option.some.inj hd2, hrel₀, pm_runChecked_steps (fun _ _ h => pm_honestB h) h₁, ?_, e1, e2, e3⟩
    rw [hp]
    trivial

theorem ExecutedIsL1PrefixWitness : Properties.ExecutedIsL1PrefixWitness := by
  obtain ⟨s, h⟩ := Option.isSome_iff_exists.mp
    (show (runChecked wParams honestB (initial wParams) (honestRun ++ honestReturn)).isSome = true by
      decide)
  have e0 : phaseTag s.phase = 6 := pm_run_proj (fun s => phaseTag s.phase) h (by decide)
  have e1 : s.d1.settling = true := pm_run_proj (fun s => s.d1.settling) h (by decide)
  have e2 : s.d2.map (fun d => d.tree.unprocessedIndex) = some 3 :=
    pm_run_proj (fun s => s.d2.map (fun d => d.tree.unprocessedIndex)) h (by decide)
  have e3 : s.executed = [11, 1, 2, 3, 4] := pm_run_proj St.executed h (by decide)
  have e4 : s.log1 = [11, 1, 2, 3, 4] := pm_run_proj St.log1 h (by decide)
  have e5 : s.d1.tree.unprocessedIndex = 5 :=
    pm_run_proj (fun s => s.d1.tree.unprocessedIndex) h (by decide)
  have e6 : s.dropped = [4] := pm_run_proj St.dropped h (by decide)
  cases hd : s.d2 with
  | none => rw [hd] at e2; cases e2
  | some d =>
    rw [hd] at e2
    exact ⟨s, d, pm_runChecked_steps (fun _ _ h => pm_honestB h) h, pm_phaseTag_back e0, e1, hd,
      Option.some.inj e2, e3, e4, e5, e6⟩

theorem ReturnMintChecksPassWitness : Properties.ReturnMintChecksPassWitness := by
  obtain ⟨s, h⟩ := Option.isSome_iff_exists.mp
    (show (runChecked wParams honestB (initial wParams)
      (honestRun ++ honestReturn.take 3)).isSome = true by decide)
  obtain ⟨c, hp, hc⟩ := pm_run_toL1 h (by decide)
  have e1 : (s.d1.pausedTs != 0) = true := pm_run_proj (fun s => s.d1.pausedTs != 0) h (by decide)
  have e2 : c.priorityTree.unprocessedIndex = 3 :=
    pm_run_toL1_proj (fun _ c => c.priorityTree.unprocessedIndex) h hc (by decide)
  have e3 : s.d1.tree.unprocessedIndex = 1 :=
    pm_run_proj (fun s => s.d1.tree.unprocessedIndex) h (by decide)
  have e4 : s.log1.length = 5 := pm_run_proj (fun s => s.log1.length) h (by decide)
  exact ⟨s, c, pm_runChecked_steps (fun _ _ h => pm_honestB h) h, hp, rfl, by simpa using e1,
    e2, e3, e4⟩

theorem ReturnRootCheckIffRootMatchWitness : Properties.ReturnRootCheckIffRootMatchWitness := by
  obtain ⟨s, h⟩ := Option.isSome_iff_exists.mp
    (show (runChecked wParams consistentB (initial wParams) honestRun).isSome = true by decide)
  obtain ⟨s', h'⟩ := Option.isSome_iff_exists.mp
    (show (runChecked wParams consistentB (initial wParams) droppedRun).isSome = true by decide)
  obtain ⟨c, hp, hc⟩ := pm_run_toL1 h (by decide)
  obtain ⟨c', hp', hc'⟩ := pm_run_toL1 h' (by decide)
  have e1 : s.d1.tree.isHistoricalRoot (lastSide c.priorityTree) = true :=
    pm_run_toL1_proj (fun s c => s.d1.tree.isHistoricalRoot (lastSide c.priorityTree)) h hc
      (by decide)
  have e2 : s'.d1.tree.isHistoricalRoot (lastSide c'.priorityTree) = false :=
    pm_run_toL1_proj (fun s c => s.d1.tree.isHistoricalRoot (lastSide c.priorityTree)) h' hc'
      (by decide)
  exact ⟨s, s', c, c', pm_runChecked_steps (fun _ _ h => pm_consistentB h) h, hp, e1,
    pm_runChecked_steps (fun _ _ h => pm_consistentB h) h', hp', e2⟩

theorem BrokenReturnNeedsRootCollisionWitness : Properties.BrokenReturnNeedsRootCollisionWitness := by
  obtain ⟨s, h⟩ := Option.isSome_iff_exists.mp
    (show (runChecked cParams consistentB (initial cParams) droppedRun).isSome = true by decide)
  obtain ⟨c, hp, hc⟩ := pm_run_toL1 h (by decide)
  have e1 : s.executed = [11, 1, 3] := pm_run_proj St.executed h (by decide)
  have e2 : s.log1 = [11, 1, 2, 3] := pm_run_proj St.log1 h (by decide)
  have e3 : s.d1.tree.isHistoricalRoot (lastSide c.priorityTree) = true :=
    pm_run_toL1_proj (fun s c => s.d1.tree.isHistoricalRoot (lastSide c.priorityTree)) h hc
      (by decide)
  have e4 : (step cParams s .l1Mint).map
      (fun s' => (s'.d1.tree.unprocessedIndex, s'.log1.drop s'.d1.tree.unprocessedIndex))
      = some (3, [3]) :=
    pm_run_proj (fun s => (step cParams s .l1Mint).map
      (fun s' => (s'.d1.tree.unprocessedIndex, s'.log1.drop s'.d1.tree.unprocessedIndex))) h
      (by decide)
  cases hs : step cParams s .l1Mint with
  | none => rw [hs] at e4; cases e4
  | some s' =>
    rw [hs] at e4
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e4
    refine ⟨s, s', c, pm_runChecked_steps (fun _ _ h => pm_consistentB h) h, hp, ?_, e3, e1, e2,
      hs, e4.1, e4.2⟩
    rw [e1, e2]
    decide

theorem ExecutedDivergencePermanentWitness : Properties.ExecutedDivergencePermanentWitness := by
  obtain ⟨s, h₀⟩ := Option.isSome_iff_exists.mp
    (show (runChecked wParams consistentB (initial wParams) (droppedRun.take 16)).isSome = true by
      decide)
  have hall : (runChecked wParams consistentB (initial wParams)
      (droppedRun.take 16 ++ (droppedRun.drop 16 ++ [.unpauseL1, .request 5]))).isSome = true := by
    rw [← List.append_assoc, List.take_append_drop]; decide
  rw [pm_run_split h₀] at hall
  obtain ⟨s', h₁⟩ := Option.isSome_iff_exists.mp hall
  have hfull : runChecked wParams consistentB (initial wParams)
      (droppedRun ++ [.unpauseL1, .request 5]) = some s' := by
    rw [← List.take_append_drop 16 droppedRun, List.append_assoc, pm_run_split h₀]; exact h₁
  have e1 : s.executed = [11, 1, 3] := pm_run_proj St.executed h₀ (by decide)
  have e2 : s.log1 = [11, 1, 2, 3] := pm_run_proj St.log1 h₀ (by decide)
  have e3 : s'.log1.length = 5 := pm_run_proj (fun s => s.log1.length) hfull (by decide)
  have e4 : phaseTag s.phase = 4 := pm_run_proj (fun s => phaseTag s.phase) h₀ (by decide)
  have e5 : phaseTag s'.phase = 5 := pm_run_proj (fun s => phaseTag s.phase) hfull (by decide)
  refine ⟨s, s', pm_runChecked_steps (fun _ _ h => pm_consistentB h) h₀,
    pm_runChecked_steps (fun _ _ h => pm_consistentB h) h₁, ?_, e1, by rw [e2]; rfl, e3, ?_⟩
  · rw [e1, e2]; decide
  · intro he
    rw [he] at e5
    rw [e4] at e5
    cases e5

theorem MigrationsDisabledKeepL1SettlingWitness :
    Properties.MigrationsDisabledKeepL1SettlingWitness := by
  obtain ⟨s, h⟩ := Option.isSome_iff_exists.mp
    (show (runChecked wParamsDisabled (fun _ _ => true) (initial wParamsDisabled)
      (failedRun.take 4)).isSome = true by decide)
  have e1 : s.log1 = [11] := pm_run_proj St.log1 h (by decide)
  have e2 : s.executed = [11] := pm_run_proj St.executed h (by decide)
  have e3 : s.d1.tree.getSize = some 0 := pm_run_proj (fun s => s.d1.tree.getSize) h (by decide)
  have e4 : inPausedWindow wParamsDisabled.migrationWindow s.d1.pausedTs s.now = true :=
    pm_run_proj (fun s => inPausedWindow wParamsDisabled.migrationWindow s.d1.pausedTs s.now) h
      (by decide)
  have e5 : decide (s.d1.batches.committed = s.d1.batches.executed) = true :=
    pm_run_proj (fun s => decide (s.d1.batches.committed = s.d1.batches.executed)) h (by decide)
  have e6 : (prepare s.d1).isSome = true := pm_run_proj (fun s => (prepare s.d1).isSome) h (by decide)
  have e7 : (step wParamsDisabled s .l1Burn).isNone = true :=
    pm_run_proj (fun s => (step wParamsDisabled s .l1Burn).isNone) h (by decide)
  exact ⟨s, pm_runChecked_steps (fun _ _ _ => trivial) h, rfl, e1, e2, e3, e4,
    of_decide_eq_true e5, e6, Option.isNone_iff_eq_none.mp e7⟩

theorem NoRelayDroppedBeforeReturnWitness : Properties.NoRelayDroppedBeforeReturnWitness := by
  obtain ⟨s₀, h₀⟩ := Option.isSome_iff_exists.mp
    (show (runChecked wParams honestB (initial wParams) (honestRun.take 9)).isSome = true by decide)
  have hall : (runChecked wParams honestB (initial wParams)
      (honestRun.take 9 ++ honestRun.drop 9)).isSome = true := by
    rw [List.take_append_drop]; decide
  rw [pm_run_split h₀] at hall
  obtain ⟨s, h₁⟩ := Option.isSome_iff_exists.mp hall
  have hfull : runChecked wParams honestB (initial wParams) honestRun = some s := by
    rw [← List.take_append_drop 9 honestRun, pm_run_split h₀]; exact h₁
  have hall2 : (runChecked wParams honestB (initial wParams)
      (honestRun ++ honestReturn)).isSome = true := by decide
  rw [pm_run_split hfull] at hall2
  obtain ⟨s', h₂⟩ := Option.isSome_iff_exists.mp hall2
  have hfull2 : runChecked wParams honestB (initial wParams) (honestRun ++ honestReturn) = some s' := by
    rw [pm_run_split hfull]; exact h₂
  have hd2 : s₀.d2.map ChainDiamond.frozen = some true :=
    pm_run_proj (fun s => s.d2.map ChainDiamond.frozen) h₀ (by decide)
  have hrel₀ : s₀.relays = [1] := pm_run_proj St.relays h₀ (by decide)
  obtain ⟨c, hp, _⟩ := pm_run_toL1 hfull (by decide)
  have e1 : s.leaves2 = [11, 1, 2] := pm_run_proj St.leaves2 hfull (by decide)
  have e2 : phaseTag s'.phase = 6 := pm_run_proj (fun s => phaseTag s.phase) hfull2 (by decide)
  have e3 : s'.dropped = [4] := pm_run_proj St.dropped hfull2 (by decide)
  cases hd : s₀.d2 with
  | none => rw [hd] at hd2; cases hd2
  | some d =>
    rw [hd] at hd2
    exact ⟨s₀, s, s', d, c, pm_runChecked_steps (fun _ _ h => pm_honestB h) h₀, hd,
      Option.some.inj hd2, hrel₀, pm_runChecked_steps (fun _ _ h => pm_honestB h) h₁, hp, e1,
      pm_runChecked_steps (fun _ _ h => pm_honestB h) h₂, pm_phaseTag_back e2, e3⟩

theorem RelayDropsIffFrozenWitness : Properties.RelayDropsIffFrozenWitness := by
  obtain ⟨s₀, h₀⟩ := Option.isSome_iff_exists.mp
    (show (runChecked wParams consistentB (initial wParams) (droppedRun.take 8)).isSome = true by
      decide)
  obtain ⟨s₁, h₁⟩ := Option.isSome_iff_exists.mp
    (show (runChecked wParams consistentB (initial wParams) (droppedRun.take 11)).isSome = true by
      decide)
  have a1 : phaseTag s₀.phase = 4 := pm_run_proj (fun s => phaseTag s.phase) h₀ (by decide)
  have a2 : s₀.relays = [1] := pm_run_proj St.relays h₀ (by decide)
  have a3 : s₀.d2.map ChainDiamond.frozen = some false :=
    pm_run_proj (fun s => s.d2.map ChainDiamond.frozen) h₀ (by decide)
  have a4 : (step wParams s₀ .relay).map (fun t => (t.leaves2, t.dropped)) = some ([11, 1], []) :=
    pm_run_proj (fun s => (step wParams s .relay).map (fun t => (t.leaves2, t.dropped))) h₀
      (by decide)
  have b1 : phaseTag s₁.phase = 4 := pm_run_proj (fun s => phaseTag s.phase) h₁ (by decide)
  have b2 : s₁.relays = [2] := pm_run_proj St.relays h₁ (by decide)
  have b3 : s₁.d2.map ChainDiamond.frozen = some true :=
    pm_run_proj (fun s => s.d2.map ChainDiamond.frozen) h₁ (by decide)
  have b4 : (step wParams s₁ .relay).map (fun t => (t.leaves2, t.dropped)) = some ([11, 1], [2]) :=
    pm_run_proj (fun s => (step wParams s .relay).map (fun t => (t.leaves2, t.dropped))) h₁
      (by decide)
  cases hd₀ : s₀.d2 with
  | none => rw [hd₀] at a3; cases a3
  | some d₀ =>
  cases hd₁ : s₁.d2 with
  | none => rw [hd₁] at b3; cases b3
  | some d₁ =>
  cases ht₀ : step wParams s₀ .relay with
  | none => rw [ht₀] at a4; cases a4
  | some t₀ =>
  cases ht₁ : step wParams s₁ .relay with
  | none => rw [ht₁] at b4; cases b4
  | some t₁ =>
    rw [hd₀] at a3
    rw [hd₁] at b3
    rw [ht₀] at a4
    rw [ht₁] at b4
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at a3 b3 a4 b4
    exact ⟨s₀, s₁, t₀, t₁, d₀, d₁, pm_runChecked_steps (fun _ _ h => pm_consistentB h) h₀,
      pm_phaseTag_onGW a1, a2, hd₀, a3, ht₀, a4.1, a4.2,
      pm_runChecked_steps (fun _ _ h => pm_consistentB h) h₁, pm_phaseTag_onGW b1, b2, hd₁, b3,
      ht₁, b4.1, b4.2⟩

theorem MirrorIffNoDropWitness : Properties.MirrorIffNoDropWitness := by
  obtain ⟨s₀, h₀⟩ := Option.isSome_iff_exists.mp
    (show (runChecked wParams (fun _ _ => true) (initial wParams) (droppedRun.take 8)).isSome = true by
      decide)
  obtain ⟨s₁, h₁⟩ := Option.isSome_iff_exists.mp
    (show (runChecked wParams (fun _ _ => true) (initial wParams)
      (droppedRun.take 15)).isSome = true by decide)
  have a1 : phaseTag s₀.phase = 4 := pm_run_proj (fun s => phaseTag s.phase) h₀ (by decide)
  have a2 : s₀.dropped = [] := pm_run_proj St.dropped h₀ (by decide)
  have a3 : s₀.leaves2 = [11] := pm_run_proj St.leaves2 h₀ (by decide)
  have a4 : s₀.relays = [1] := pm_run_proj St.relays h₀ (by decide)
  have a5 : s₀.log1 = [11, 1] := pm_run_proj St.log1 h₀ (by decide)
  have b1 : phaseTag s₁.phase = 4 := pm_run_proj (fun s => phaseTag s.phase) h₁ (by decide)
  have b2 : s₁.dropped = [2] := pm_run_proj St.dropped h₁ (by decide)
  have b3 : s₁.leaves2 = [11, 1, 3] := pm_run_proj St.leaves2 h₁ (by decide)
  have b4 : s₁.relays = [] := pm_run_proj St.relays h₁ (by decide)
  have b5 : s₁.log1 = [11, 1, 2, 3] := pm_run_proj St.log1 h₁ (by decide)
  exact ⟨s₀, s₁, pm_runChecked_steps (fun _ _ _ => trivial) h₀, pm_phaseTag_onGW a1, a2, a3, a4, a5,
    pm_runChecked_steps (fun _ _ _ => trivial) h₁, pm_phaseTag_onGW b1, b2, b3, b4, b5⟩

theorem MirrorBreakPermanentWitness : Properties.MirrorBreakPermanentWitness := by
  obtain ⟨s, h₀⟩ := Option.isSome_iff_exists.mp
    (show (runChecked wParams (fun _ _ => true) (initial wParams)
      (droppedRun.take 12)).isSome = true by decide)
  have hall : (runChecked wParams (fun _ _ => true) (initial wParams)
      (droppedRun.take 12 ++ droppedRun.drop 12)).isSome = true := by
    rw [List.take_append_drop]; decide
  rw [pm_run_split h₀] at hall
  obtain ⟨s', h₁⟩ := Option.isSome_iff_exists.mp hall
  have hfull : runChecked wParams (fun _ _ => true) (initial wParams) droppedRun = some s' := by
    rw [← List.take_append_drop 12 droppedRun, pm_run_split h₀]; exact h₁
  have e1 : s.dropped = [2] := pm_run_proj St.dropped h₀ (by decide)
  have e2 : s.relays = [] := pm_run_proj St.relays h₀ (by decide)
  obtain ⟨c, hp, _⟩ := pm_run_toL1 hfull (by decide)
  have e3 : s'.log1 = [11, 1, 2, 3] := pm_run_proj St.log1 hfull (by decide)
  have e4 : s'.leaves2 = [11, 1, 3] := pm_run_proj St.leaves2 hfull (by decide)
  exact ⟨s, s', c, pm_runChecked_steps (fun _ _ _ => trivial) h₀,
    pm_runChecked_steps (fun _ _ _ => trivial) h₁, e1, e2, hp, e3, e4⟩

theorem ReturnMintPassesOnPrefixWitness : Properties.ReturnMintPassesOnPrefixWitness := by
  obtain ⟨s, h₀⟩ := Option.isSome_iff_exists.mp
    (show (runChecked wParams consistentB (initial wParams) (recoveredRun.take 16)).isSome = true by
      decide)
  have hall : (runChecked wParams consistentB (initial wParams)
      (recoveredRun.take 16 ++ recoveredRun.drop 16)).isSome = true := by
    rw [List.take_append_drop]; decide
  rw [pm_run_split h₀] at hall
  obtain ⟨s', h₁⟩ := Option.isSome_iff_exists.mp hall
  have hfull : runChecked wParams consistentB (initial wParams) recoveredRun = some s' := by
    rw [← List.take_append_drop 16 recoveredRun, pm_run_split h₀]; exact h₁
  obtain ⟨c, hp, _⟩ := pm_run_toL1 h₀ (by decide)
  have e1 : (s.d1.pausedTs != 0) = true := pm_run_proj (fun s => s.d1.pausedTs != 0) h₀ (by decide)
  have e2 : s.dropped = [2] := pm_run_proj St.dropped h₀ (by decide)
  have e3 : s.executed = [11, 1] := pm_run_proj St.executed h₀ (by decide)
  have e4 : s.log1 = [11, 1, 2] := pm_run_proj St.log1 h₀ (by decide)
  have e5 : phaseTag s'.phase = 6 := pm_run_proj (fun s => phaseTag s.phase) hfull (by decide)
  have e6 : s'.executed = [11, 1, 2] := pm_run_proj St.executed hfull (by decide)
  refine ⟨s, s', c, pm_runChecked_steps (fun _ _ h => pm_consistentB h) h₀, hp, rfl,
    by simpa using e1, e2, e3, e4, ?_, pm_runChecked_steps (fun _ _ h => pm_consistentB h) h₁,
    pm_phaseTag_back e5, e6⟩
  rw [e3, e4]
  decide

/-! ## The countermodel -/

theorem DroppedRelayCountermodel : Properties.DroppedRelayCountermodel := by
  obtain ⟨s₀, h₀⟩ := Option.isSome_iff_exists.mp
    (show (runChecked wParams consistentB (initial wParams) (droppedRun.take 11)).isSome = true by
      decide)
  have hall : (runChecked wParams consistentB (initial wParams)
      (droppedRun.take 11 ++ droppedRun.drop 11)).isSome = true := by
    rw [List.take_append_drop]; decide
  rw [pm_run_split h₀] at hall
  obtain ⟨s, h₁⟩ := Option.isSome_iff_exists.mp hall
  have hfull : runChecked wParams consistentB (initial wParams) droppedRun = some s := by
    rw [← List.take_append_drop 11 droppedRun, pm_run_split h₀]; exact h₁
  -- the first remaining step is the relay of `2`
  have hdrop : droppedRun.drop 11 = .relay :: droppedRun.drop 12 := rfl
  rw [hdrop] at h₁
  unfold runChecked at h₁
  split at h₁
  · split at h₁
    · cases h₁
    · rename_i s₁ hs₁
      have hd2 : s₀.d2.map ChainDiamond.frozen = some true :=
        pm_run_proj (fun s => s.d2.map ChainDiamond.frozen) h₀ (by decide)
      have hrel₀ : s₀.relays = [2] := pm_run_proj St.relays h₀ (by decide)
      have hdr : (step wParams s₀ .relay).map St.dropped = some [2] :=
        pm_run_proj (fun s => (step wParams s .relay).map St.dropped) h₀ (by decide)
      rw [hs₁] at hdr
      obtain ⟨c, hp, hc⟩ := pm_run_toL1 hfull (by decide)
      have e1 : s.log1 = [11, 1, 2, 3] := pm_run_proj St.log1 hfull (by decide)
      have e2 : s.leaves2 = [11, 1, 3] := pm_run_proj St.leaves2 hfull (by decide)
      have e3 : s.executed = [11, 1, 3] := pm_run_proj St.executed hfull (by decide)
      have e4 : (s.d1.pausedTs != 0) = true :=
        pm_run_proj (fun s => s.d1.pausedTs != 0) hfull (by decide)
      have e5 : s.d1.tree.isHistoricalRoot (lastSide c.priorityTree) = false :=
        pm_run_toL1_proj (fun s c => s.d1.tree.isHistoricalRoot (lastSide c.priorityTree))
          hfull hc (by decide)
      have e6 : (s.d1.tree.l1Reinit c.priorityTree).isSome = true :=
        pm_run_toL1_proj (fun s c => (s.d1.tree.l1Reinit c.priorityTree).isSome) hfull hc
          (by decide)
      have e7 : (mintBatches s.d1.batches c).isSome = true :=
        pm_run_toL1_proj (fun s c => (mintBatches s.d1.batches c).isSome) hfull hc (by decide)
      have e8 : (step wParams s .l1Mint).isNone = true :=
        pm_run_proj (fun s => (step wParams s .l1Mint).isNone) hfull (by decide)
      cases hd : s₀.d2 with
      | none => rw [hd] at hd2; cases hd2
      | some d =>
        rw [hd] at hd2
        refine ⟨s₀, s₁, s, d, c, pm_runChecked_steps (fun _ _ h => pm_consistentB h) h₀, hd,
          Option.some.inj hd2, hrel₀, hs₁, Option.some.inj hdr,
          pm_runChecked_steps (fun _ _ h => pm_consistentB h) h₁, hp, e1, e2, e3, ?_,
          by simpa using e4, e5, e6, e7, Option.isNone_iff_eq_none.mp e8⟩
        rw [e1, e3]
        decide
  · cases h₁

end Protocol.PriorityMirror
