import EraSpec.Protocol.InteropAtomicity.Properties.BatchPosition
import EraSpec.Protocol.InteropAtomicity.Proofs.Timeout
import EraSpec.Contracts.AtomicInteropProof.Proofs.LastLeaf

/-!
# Proofs: the END-branch composition with leaf position and batch number apart

The last-position argument is reused unchanged
(`MerkleSpec.LastLeaf.accepted_last_leaf_or_pinned_break`), and the leaf is pinned to the
entry stored at the position (`MerkleSpec.Verifier.accept_pins_entry_or_collision`).  What
is new is one step, `last_position_fixes_batch_number`: an entry's leaf is
`batchLeafHash` of its preimage, so equal leaves at the last position mean the submitted
preimage is the last entry, unless the two preimages collide.  From there the old chain
runs as before (`Contracts.Timeout.refundableBy_of_verifiedBy`,
`timeout_means_missed_deadline_or_break`).
-/

namespace Contracts.BatchPosition

open Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Timeout
open MerkleSpec MerkleSpec.LastLeaf MerkleSpec.Verifier IMTAbstract

/-! ## The numbering discipline of `MessageRootBase` -/

/-- What every reachable slot satisfies.  `aboveStart`: a pushed batch is after the
starting batch, unless it is a ZKsync OS chain's genesis batch `0`. -/
structure SlotInv (zksyncOS : Bool) (s : ℕ) (σ : ChainTreeSlot) : Prop where
  increasing : σ.pushed.Pairwise (fun a b => a.batchNumber < b.batchNumber)
  pushedRecorded : ∀ e ∈ σ.pushed, σ.recorded e.batchNumber = true
  recordedBelow : ∀ n, σ.recorded n = true → n ≤ σ.current
  startBelow : s ≤ σ.current
  aboveStart : ∀ e ∈ σ.pushed, s < e.batchNumber ∨ (zksyncOS = true ∧ s = 0 ∧ e.batchNumber = 0)

lemma slotInv_registered (zksyncOS : Bool) (s : ℕ) : SlotInv zksyncOS s (registeredSlot s) where
  increasing := List.Pairwise.nil
  pushedRecorded := fun _ he => absurd he List.not_mem_nil
  recordedBelow := fun _ hn => absurd hn Bool.false_ne_true
  startBelow := le_refl s
  aboveStart := fun _ he => absurd he List.not_mem_nil

private lemma update_true_le {f : ℕ → Bool} {n m cur : ℕ} (hf : ∀ k, f k = true → k ≤ cur)
    (hn : cur ≤ n) (hm : Function.update f n true m = true) : m ≤ n := by
  by_cases hmn : m = n
  · exact le_of_eq hmn
  · rw [Function.update_of_ne hmn] at hm
    exact le_trans (hf m hm) hn

lemma slotInv_step {zksyncOS : Bool} {s : ℕ} {σ τ : ChainTreeSlot} (hσ : SlotInv zksyncOS s σ)
    (hst : ChainTreeStep zksyncOS σ τ) : SlotInv zksyncOS s τ := by
  cases hst with
  | recordOnly n _ hn =>
    refine ⟨hσ.increasing, ?_, ?_, ?_, hσ.aboveStart⟩
    · intro e he
      dsimp only at he ⊢
      by_cases hen : e.batchNumber = n
      · rw [hen, Function.update_self]
      · rw [Function.update_of_ne hen]
        exact hσ.pushedRecorded e he
    · intro m hm
      dsimp only at hm ⊢
      exact update_true_le hσ.recordedBelow (by omega) hm
    · have := hσ.startBelow
      show s ≤ n
      omega
  | recordAndPush n root ts _ hn =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show (σ.pushed ++ [⟨root, n, ts⟩]).Pairwise _
      rw [List.pairwise_append]
      refine ⟨hσ.increasing, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      have := hσ.recordedBelow _ (hσ.pushedRecorded a ha)
      show a.batchNumber < n
      omega
    · intro e he
      dsimp only at he ⊢
      by_cases hen : e.batchNumber = n
      · rw [hen, Function.update_self]
      · rw [Function.update_of_ne hen]
        rcases List.mem_append.mp he with he | he
        · exact hσ.pushedRecorded e he
        · rw [List.mem_singleton] at he
          subst he
          exact absurd rfl hen
    · intro m hm
      dsimp only at hm ⊢
      exact update_true_le hσ.recordedBelow (by omega) hm
    · have := hσ.startBelow
      show s ≤ n
      omega
    · intro e he
      dsimp only at he
      rcases List.mem_append.mp he with he | he
      · exact hσ.aboveStart e he
      · rw [List.mem_singleton] at he
        subst he
        have := hσ.startBelow
        left
        show s < n
        omega
  | migrate n hle =>
    exact ⟨hσ.increasing, hσ.pushedRecorded, fun m hm => le_trans (hσ.recordedBelow m hm) hle,
      le_trans hσ.startBelow hle, hσ.aboveStart⟩
  | seedGenesis root ts hos hcur hrec0 =>
    have hempty : σ.pushed = [] := by
      rcases List.eq_nil_or_concat σ.pushed with hnil | ⟨L, e, hLe⟩
      · exact hnil
      · exfalso
        have hmem : e ∈ σ.pushed := by rw [hLe]; simp
        have h1 := hσ.pushedRecorded e hmem
        have h2 := hσ.recordedBelow _ h1
        rw [hcur] at h2
        have h0 : e.batchNumber = 0 := by omega
        rw [h0, hrec0] at h1
        exact Bool.false_ne_true h1
    have hs0 : s = 0 := by have := hσ.startBelow; omega
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show (σ.pushed ++ [⟨root, 0, ts⟩]).Pairwise _
      rw [hempty]
      exact List.pairwise_singleton _ _
    · intro e he
      have he' : e ∈ σ.pushed ++ [⟨root, 0, ts⟩] := he
      rw [hempty, List.nil_append, List.mem_singleton] at he'
      subst he'
      exact Function.update_self _ _ _
    · intro m hm
      dsimp only at hm ⊢
      exact update_true_le (cur := σ.current) hσ.recordedBelow (by omega) hm
    · show s ≤ 0
      omega
    · intro e he
      have he' : e ∈ σ.pushed ++ [⟨root, 0, ts⟩] := he
      rw [hempty, List.nil_append, List.mem_singleton] at he'
      subst he'
      exact Or.inr ⟨hos, hs0, rfl⟩

theorem slotInv_of_reachable {zksyncOS : Bool} {s : ℕ} {σ : ChainTreeSlot}
    (hr : SlotReachable zksyncOS s σ) : SlotInv zksyncOS s σ := by
  induction hr with
  | refl => exact slotInv_registered zksyncOS s
  | tail _ hst ih => exact slotInv_step ih hst

theorem reachable_slot_numbers_increase {zksyncOS : Bool} {s : ℕ} {σ : ChainTreeSlot}
    (hr : SlotReachable zksyncOS s σ) :
    σ.pushed.Pairwise (fun a b => a.batchNumber < b.batchNumber) :=
  (slotInv_of_reachable hr).increasing

theorem tree_above_start_without_genesis {zksyncOS : Bool} {s : ℕ} {σ : ChainTreeSlot}
    (hr : SlotReachable zksyncOS s σ) (hng : zksyncOS = false ∨ 0 < s) :
    ∀ e ∈ σ.pushed, s < e.batchNumber := by
  intro e he
  rcases (slotInv_of_reachable hr).aboveStart e he with hlt | ⟨hos, hs, _⟩
  · exact hlt
  · rcases hng with hng | hng
    · rw [hng] at hos
      exact absurd hos Bool.false_ne_true
    · omega

/-- A strictly increasing list of batch numbers, all above `k`: index `i` holds a number above
`k + i`. -/
theorem index_lt_batchNumber : ∀ (l : List BatchEntry) (k : ℕ),
    l.Pairwise (fun a b => a.batchNumber < b.batchNumber) → (∀ e ∈ l, k < e.batchNumber) →
      ∀ (i : ℕ) (hi : i < l.length), k + i < (l[i]'hi).batchNumber
  | [], _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | a :: _, _, _, hk, 0, _ => by
      simpa using hk a List.mem_cons_self
  | a :: t, k, hpw, hk, i + 1, hi => by
      rw [List.pairwise_cons] at hpw
      have ht : ∀ e ∈ t, k + 1 < e.batchNumber := fun e he => by
        have h1 := hpw.1 e he
        have h2 := hk a List.mem_cons_self
        omega
      have := index_lt_batchNumber t (k + 1) hpw.2 ht i (by simpa using hi)
      simp only [List.getElem_cons_succ]
      omega

theorem tree_position_below_batch_number {zksyncOS : Bool} {s : ℕ} {σ : ChainTreeSlot}
    (hr : SlotReachable zksyncOS s σ) (hng : zksyncOS = false ∨ 0 < s) :
    ∀ (i : ℕ) (hi : i < σ.pushed.length), s + i < (σ.pushed[i]'hi).batchNumber :=
  index_lt_batchNumber σ.pushed s (reachable_slot_numbers_increase hr)
    (tree_above_start_without_genesis hr hng)

/-- `addNewChain(c, s)` then one `addChainBatchRootV32(c, s + 1, root)`. -/
theorem onboardedSlot_reachable (zksyncOS : Bool) (s : ℕ) (root : UInt256) (ts : ℕ) :
    SlotReachable zksyncOS s (onboardedSlot s root ts) :=
  Relation.ReflTransGen.single
    (ChainTreeStep.recordAndPush (registeredSlot s) (s + 1) root ts rfl rfl)

theorem reachable_slots_back_a_root (h : Hash) (ze : UInt256) (bl : BatchLeafHash)
    (zksyncOS : Chain → Bool) (s : Chain → ℕ) (σ : Chain → ChainTreeSlot) (created : ℕ)
    (height : Chain → ℕ) (hr : ∀ c, SlotReachable (zksyncOS c) (s c) (σ c))
    (hcap : ∀ c, (σ c).pushed.length ≤ 2 ^ height c) :
    ∃ B : PositionedBacking h ze bl (slotRoot σ created),
      ∀ c, B.entries c = (σ c).pushed ∧ B.height c = height c :=
  ⟨{ entries := fun c => (σ c).pushed
     height := height
     numbersIncrease := fun c => reachable_slot_numbers_increase (hr c)
     upToLast := fun c e he => by simp [slotRoot, he]
     capacity := hcap }, fun _ => ⟨rfl, rfl⟩⟩

/-! ## The old composition at a one-leaf tree -/

theorem current_composition_cannot_represent_onboarding_at_100 :
    Properties.CurrentCompositionCannotRepresentOnboardingAt100 := by
  refine ⟨fun zksyncOS root ts => ⟨onboardedSlot_reachable zksyncOS 100 root ts, rfl⟩, ?_⟩
  intro h ze R B c hlen
  have hup : R.upTo c = 0 := by
    have := B.upToLast c
    omega
  refine ⟨hup, ?_, ?_, ?_⟩
  · intro S D N sibs x ha
    have := ha.lastBatch.inRange
    omega
  · intro S D sibs x ha
    have := ha.lastBatch.inRange
    omega
  · intro S h101 hagg
    have := hagg c 101 h101
    omega

/-! ## Facts about a positioned backing -/

section Backing

variable {h : Hash} {ze : UInt256} {bl : BatchLeafHash} {R : SlRoot}

lemma leaves_length (B : PositionedBacking h ze bl R) (c : Chain) :
    (B.leaves c).length = (B.entries c).length :=
  List.length_map _

lemma leaves_getD_of_lt (B : PositionedBacking h ze bl R) (c : Chain) {pos : ℕ}
    (hpos : pos < (B.entries c).length) :
    (B.leaves c).getD pos ze = entryLeaf bl (B.entryAt c pos) := by
  simp [PositionedBacking.leaves, PositionedBacking.entryAt, List.getD_eq_getElem?_getD, hpos]

lemma leaves_getD_of_le (B : PositionedBacking h ze bl R) (c : Chain) {pos : ℕ}
    (hpos : (B.entries c).length ≤ pos) : (B.leaves c).getD pos ze = ze := by
  simp [PositionedBacking.leaves, List.getD_eq_getElem?_getD, hpos]

lemma entryAt_mem (B : PositionedBacking h ze bl R) (c : Chain) {pos : ℕ}
    (hpos : pos < (B.entries c).length) : B.entryAt c pos ∈ B.entries c := by
  have he : B.entryAt c pos = (B.entries c)[pos] := by
    simp [PositionedBacking.entryAt, List.getD_eq_getElem?_getD, hpos]
  rw [he]
  exact List.getElem_mem hpos

lemma entryAt_last (B : PositionedBacking h ze bl R) (c : Chain) {pos : ℕ}
    (hlast : pos + 1 = (B.entries c).length) :
    (B.entries c).getLast? = some (B.entryAt c pos) := by
  have hpos : pos < (B.entries c).length := by omega
  rw [List.getLast?_eq_getElem?, show (B.entries c).length - 1 = pos from by omega]
  simp [PositionedBacking.entryAt, List.getD_eq_getElem?_getD, hpos]

theorem entry_le_upTo (B : PositionedBacking h ze bl R) (c : Chain) :
    ∀ e ∈ B.entries c, e.batchNumber ≤ R.upTo c := by
  intro e he
  have hne : B.entries c ≠ [] := List.ne_nil_of_mem he
  have hlast := B.upToLast c _ (List.getLast?_eq_some_getLast hne)
  have hpw := B.numbersIncrease c
  have hsplit := List.dropLast_append_getLast hne
  rw [← hsplit] at hpw he
  rcases List.mem_append.mp he with hin | hin
  · have := (List.pairwise_append.mp hpw).2.2 e hin _ (List.mem_singleton_self _)
    omega
  · rw [List.mem_singleton] at hin
    rw [hin]
    exact le_of_eq hlast

end Backing

/-! ## The last-batch proof, position and number apart -/

section LastBatch

variable {h : Hash} {ze : UInt256} {bl : BatchLeafHash} {R : SlRoot}

/-- **THE LAST POSITION FIXES THE BATCH NUMBER, OR A NAMED LEAF COLLISION.** -/
theorem last_position_fixes_batch_number (B : PositionedBacking h ze bl R) (c : Chain)
    {pos : ℕ} {r : UInt256} {N t : ℕ} (hlast : pos + 1 = (B.entries c).length)
    (hleaf : (B.leaves c).getD pos ze = bl r N t) :
    SubmittedIsLastEntry B c r N t ∨ LeafPreimageClash bl (B.entryAt c pos) ⟨r, N, t⟩ := by
  have hpos : pos < (B.entries c).length := by omega
  rw [leaves_getD_of_lt B c hpos] at hleaf
  by_cases heq : B.entryAt c pos = ⟨r, N, t⟩
  · left
    unfold SubmittedIsLastEntry
    rw [entryAt_last B c hlast, heq]
  · exact Or.inr ⟨heq, hleaf⟩

theorem submitted_last_is_upTo {B : PositionedBacking h ze bl R} {c : Chain} {r : UInt256}
    {N t : ℕ} (hs : SubmittedIsLastEntry B c r N t) : N = R.upTo c :=
  B.upToLast c _ hs

theorem submitted_last_timed {B : PositionedBacking h ze bl R} {S : System} {c : Chain}
    {r : UInt256} {N t : ℕ} (hT : EntriesTimed S B) (hs : SubmittedIsLastEntry B c r N t) :
    S.time c N = t :=
  hT c _ (List.mem_of_getLast? hs)

theorem mask_bound_gives_occupied_range (B : PositionedBacking h ze bl R) (c : Chain)
    {pos : ℕ} {sibs : ℕ → UInt256} {r : UInt256} {N t : ℕ} (hmask : pos < 2 ^ B.height c)
    (hw : walkPure h sibs 0 (B.height c) pos (bl r N t) = rootOf h ze (B.leaves c) (B.height c)) :
    pos < (B.entries c).length ∨ bl r N t = ze
      ∨ PathCollision h ze (B.leaves c) sibs 0 (B.height c) pos (bl r N t) := by
  rcases accept_pins_entry_or_collision h ze (B.leaves c) sibs (B.height c) pos (bl r N t)
      hmask hw with he | hc
  · by_cases hpos : pos < (B.entries c).length
    · exact Or.inl hpos
    · rw [leaves_getD_of_le B c (by omega)] at he
      exact Or.inr (Or.inl he.symm)
  · exact Or.inr (Or.inr hc)

/-- **AN ACCEPTED LAST-BATCH PROOF IDENTIFIES THE LAST ENTRY, OR PINS A BREAK.** -/
theorem positioned_lastBatch_pinned {B : PositionedBacking h ze bl R} {c : Chain} {pos : ℕ}
    {sibs : ℕ → UInt256} {r : UInt256} {N t : ℕ}
    (ha : PositionedLastBatchAccepted B c pos sibs r N t) :
    SubmittedIsLastEntry B c r N t ∨ PositionedEndBreak B c pos sibs r N t := by
  have hlenL := leaves_length B c
  have hcap : (B.leaves c).length ≤ 2 ^ B.height c := by
    rw [hlenL]
    exact B.capacity c
  have hin : pos < (B.leaves c).length := by
    rw [hlenL]
    exact ha.inRange
  rcases accepted_last_leaf_or_pinned_break h ze (B.leaves c) sibs (B.height c) pos (bl r N t)
      hcap hin ha.authenticated ha.zeroRightSiblings with hlast | hpb | hpc
  · rcases accept_pins_entry_or_collision h ze (B.leaves c) sibs (B.height c) pos (bl r N t)
        (lt_of_lt_of_le hin hcap) ha.authenticated with hleaf | hpc
    · rcases last_position_fixes_batch_number B c (by omega) hleaf with hs | hclash
      · exact Or.inl hs
      · exact Or.inr (Or.inr (Or.inr hclash))
    · exact Or.inr (Or.inr (Or.inl hpc))
  · exact Or.inr (Or.inl hpb)
  · exact Or.inr (Or.inr (Or.inl hpc))

/-- **THE BREAKS ARE EXCLUDED BY A BOUNDED PREMISE.** -/
theorem no_positioned_end_break_on {B : PositionedBacking h ze bl R} {c : Chain} {pos : ℕ}
    {sibs : ℕ → UInt256} {r : UInt256} {N t : ℕ} (hpos : pos < (B.entries c).length)
    (hsep : EntriesNotEmpty ze (B.leaves c))
    (hinj : PairInjOn h (fun p => TreePair h ze (B.leaves c) (B.height c) p
      ∨ VerifiedPair h sibs (B.height c) pos (bl r N t) p))
    (hleaf : BatchLeafInjOn bl (LeafPreimage B c r N t)) :
    ¬ PositionedEndBreak B c pos sibs r N t := by
  have hlenL := leaves_length B c
  have hcap : (B.leaves c).length ≤ 2 ^ B.height c := by
    rw [hlenL]
    exact B.capacity c
  rintro (hpb | ⟨i, hi, hne, heq⟩ | ⟨hne, heq⟩)
  · exact no_pinned_break_on h ze (B.leaves c) (B.height c) pos hcap hsep
      (pairInjOn_mono hinj (fun p hp => Or.inl hp)) hpb
  · exact hne (hinj _ _ (Or.inr ⟨i, hi, rfl⟩)
      (Or.inl (treePair_mem h ze (B.leaves c) (B.height c) pos i (by rw [hlenL]; exact hpos) hi))
      heq)
  · exact hne (hleaf _ _ (Or.inl (entryAt_mem B c hpos)) (Or.inr rfl) heq)

/-- **UNDER THE BOUNDED PREMISE, THE ACCEPTED PROOF NAMES THE LAST BATCH.** -/
theorem positioned_lastBatch_on {B : PositionedBacking h ze bl R} {c : Chain} {pos : ℕ}
    {sibs : ℕ → UInt256} {r : UInt256} {N t : ℕ} (hsep : EntriesNotEmpty ze (B.leaves c))
    (hinj : PairInjOn h (fun p => TreePair h ze (B.leaves c) (B.height c) p
      ∨ VerifiedPair h sibs (B.height c) pos (bl r N t) p))
    (hleaf : BatchLeafInjOn bl (LeafPreimage B c r N t))
    (ha : PositionedLastBatchAccepted B c pos sibs r N t) :
    SubmittedIsLastEntry B c r N t ∧ N = R.upTo c := by
  rcases positioned_lastBatch_pinned ha with hs | hb
  · exact ⟨hs, submitted_last_is_upTo hs⟩
  · exact absurd hb (no_positioned_end_break_on ha.inRange hsep hinj hleaf)

/-- **THE END BRANCH AS RUN IMPLIES THE END BRANCH AS ASSUMED, OR PINS A BREAK.** -/
theorem positioned_endBranch_verified_pinned {B : PositionedBacking h ze bl R} {S : System}
    {c : Chain} {D pos : ℕ} {sibs : ℕ → UInt256} {r : UInt256} {N t : ℕ}
    (hT : EntriesTimed S B) (ha : PositionedEndBranchAccepted B c D pos sibs r N t) :
    EndBranchVerified S R c D N ∨ PositionedEndBreak B c pos sibs r N t := by
  rcases positioned_lastBatch_pinned ha.lastBatch with hs | hb
  · refine Or.inl ⟨ha.rootAfterDeadline, ?_, submitted_last_is_upTo hs⟩
    rw [submitted_last_timed hT hs]
    exact ha.onTime
  · exact Or.inr hb

theorem positioned_endBranch_verified_on {B : PositionedBacking h ze bl R} {S : System}
    {c : Chain} {D pos : ℕ} {sibs : ℕ → UInt256} {r : UInt256} {N t : ℕ}
    (hT : EntriesTimed S B) (hsep : EntriesNotEmpty ze (B.leaves c))
    (hinj : PairInjOn h (fun p => TreePair h ze (B.leaves c) (B.height c) p
      ∨ VerifiedPair h sibs (B.height c) pos (bl r N t) p))
    (hleaf : BatchLeafInjOn bl (LeafPreimage B c r N t))
    (ha : PositionedEndBranchAccepted B c D pos sibs r N t) : EndBranchVerified S R c D N := by
  rcases positioned_endBranch_verified_pinned hT ha with hv | hb
  · exact hv
  · exact absurd hb (no_positioned_end_break_on ha.lastBatch.inRange hsep hinj hleaf)

end LastBatch

/-! ## The gate -/

section Gate

variable {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue} {S : System}
  {ze : UInt256} {bl : BatchLeafHash} {R : SlRoot} {B : PositionedBacking h ze bl R}
  {F : Flow} {leg : FlowLeg} {N : ℕ} {p : ImtProof} {pos : ℕ} {sibs : ℕ → UInt256}
  {r : UInt256} {t : ℕ}

/-- The positioned gate is the verified gate, or its END branch carries a break. -/
theorem verifiedBy_of_positioned (hT : EntriesTimed S B)
    (ha : PositionedLegRefundableAcceptedBy h z0 hl cv S B F leg N p pos sibs r t) :
    LegRefundableVerifiedBy h z0 hl cv S R F leg N p
      ∨ (PositionedEndBranchAccepted B leg.chain F.deadline pos sibs r N t
          ∧ PositionedEndBreak B leg.chain pos sibs r N t) := by
  rcases ha with ⟨hb, habs⟩ | ⟨he, habs⟩
  · exact Or.inl (Or.inl ⟨hb, habs⟩)
  · rcases positioned_endBranch_verified_pinned hT he with hv | hbr
    · exact Or.inl (Or.inr ⟨hv, habs⟩)
    · exact Or.inr ⟨he, hbr⟩

theorem positioned_accepted_implies_refundable_pinned (hagg : Aggregates S R)
    (hT : EntriesTimed S B)
    (ha : PositionedLegRefundableAcceptedBy h z0 hl cv S B F leg N p pos sibs r t) :
    LegRefundableBy h z0 hl cv S F leg N p
      ∨ (PositionedEndBranchAccepted B leg.chain F.deadline pos sibs r N t
          ∧ PositionedEndBreak B leg.chain pos sibs r N t) := by
  rcases verifiedBy_of_positioned hT ha with hv | hrest
  · exact Or.inl (refundableBy_of_verifiedBy hagg hv)
  · exact Or.inr hrest

theorem positioned_accepted_implies_refundable_on (hagg : Aggregates S R)
    (hT : EntriesTimed S B) (hsep : EntriesNotEmpty ze (B.leaves leg.chain))
    (hinj : PairInjOn h (fun q => TreePair h ze (B.leaves leg.chain) (B.height leg.chain) q
      ∨ VerifiedPair h sibs (B.height leg.chain) pos (bl r N t) q))
    (hleaf : BatchLeafInjOn bl (LeafPreimage B leg.chain r N t))
    (ha : PositionedLegRefundableAcceptedBy h z0 hl cv S B F leg N p pos sibs r t) :
    LegRefundableBy h z0 hl cv S F leg N p := by
  rcases positioned_accepted_implies_refundable_pinned hagg hT ha with hr | ⟨he, hb⟩
  · exact hr
  · exact absurd hb (no_positioned_end_break_on he.lastBatch.inRange hsep hinj hleaf)

theorem positioned_timeout_means_missed_deadline_or_break (hS : Wf S) (hagg : Aggregates S R)
    (hT : EntriesTimed S B)
    (ha : PositionedLegRefundableAcceptedBy h z0 hl cv S B F leg N p pos sibs r t) :
    (∀ n, S.time leg.chain n ≤ F.deadline →
        legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)))
      ∨ AbsenceBreak h z0 hl S F.deadline leg.chain N p
      ∨ (PositionedEndBranchAccepted B leg.chain F.deadline pos sibs r N t
          ∧ PositionedEndBreak B leg.chain pos sibs r N t) := by
  rcases verifiedBy_of_positioned hT ha with hv | hrest
  · rcases timeout_means_missed_deadline_or_break hS hagg hv with hm | hb
    · exact Or.inl hm
    · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr hrest)

end Gate

/-! ## The settlement layer's side, over the batches pushed -/

section PushLog

variable {h : Hash} {ze : UInt256} {bl : BatchLeafHash} {R : SlRoot}

theorem aggregates_from_pushLog {B : PositionedBacking h ze bl R} {S : System} {P : PushLog}
    (hpush : AggregatesPushed P B) (hclk : ClockFromPushes S P)
    (hgap : GapsAfterRootLate S P R) : Aggregates S R := by
  intro c m hm
  by_contra hcon
  have hafter : R.upTo c < m := Nat.lt_of_not_le hcon
  by_cases hp : ∃ e, P c e ∧ e.batchNumber = m
  · obtain ⟨e, hPe, hem⟩ := hp
    have htime : S.time c m = e.l1Timestamp := by
      rw [← hem]
      exact hclk c e hPe
    have hin : e ∈ B.entries c := hpush c e hPe (by rw [← htime]; exact hm)
    have := entry_le_upTo B c e hin
    omega
  · have := hgap c m hafter (fun e hPe hem => hp ⟨e, hPe, hem⟩)
    omega

theorem entriesTimed_from_pushLog {B : PositionedBacking h ze bl R} {S : System} {P : PushLog}
    (hroot : RootEntriesPushed P B) (hclk : ClockFromPushes S P) : EntriesTimed S B :=
  fun c e he => hclk c e (hroot c e he)

end PushLog

/-! ## Witnesses: the composition at an offset -/

lemma onboarded_pairs_mem (p : UInt256 × UInt256)
    (hp : TreePair demoHash 0 [5] 1 p
      ∨ VerifiedPair demoHash (honestSibs demoHash 0 [5] 0) 1 0 5 p) :
    p ∈ ([(5, 0), (0, 0)] : List (UInt256 × UInt256)) := by
  rcases hp with (⟨l, hl, m, hm, rfl⟩ | ⟨l, hl, rfl⟩) | ⟨i, hi, rfl⟩
  · interval_cases l
    have : m = 0 := by simp at hm; omega
    subst this
    decide
  · interval_cases l
    decide
  · interval_cases i
    decide

/-- The one-leaf tree `[5]` at height 1 meets the bounded no-collision premise under the
colliding `demoHash`. -/
theorem onboarded_pairInjOn : PairInjOn demoHash (fun p => TreePair demoHash 0 [5] 1 p
    ∨ VerifiedPair demoHash (honestSibs demoHash 0 [5] 0) 1 0 5 p) := by
  have hW : ∀ p ∈ ([(5, 0), (0, 0)] : List (UInt256 × UInt256)),
      ∀ q ∈ ([(5, 0), (0, 0)] : List (UInt256 × UInt256)),
        demoHash p.1 p.2 = demoHash q.1 q.2 → p = q := by
    intro p hp q hq he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
      first | rfl | exact absurd he (by decide)
  exact fun p q hp hq he => hW p (onboarded_pairs_mem p hp) q (onboarded_pairs_mem q hq) he

theorem onboarded_entriesNotEmpty : EntriesNotEmpty 0 [5] := by
  intro m hm
  simp only [List.length_cons, List.length_nil] at hm
  interval_cases m
  decide

theorem onboarded_endBranch (s : ℕ) (c : Chain) :
    PositionedEndBranchAccepted (onboardedBacking s) c 0 0 (honestSibs demoHash 0 [5] 0) 5
      (s + 1) 0 where
  rootAfterDeadline := by show 0 < 1; norm_num
  onTime := le_refl 0
  lastBatch :=
    { inRange := by show 0 < 1; norm_num
      authenticated := honest_walk_root demoHash 0 [5] 1 0 (by norm_num)
      zeroRightSiblings := by
        intro l hl _
        have hl1 : l < 1 := hl
        obtain rfl : l = 0 := by omega
        decide }

theorem onboarded_leafInj (s : ℕ) (c : Chain) :
    BatchLeafInjOn rootLeaf (LeafPreimage (onboardedBacking s) c 5 (s + 1) 0) := by
  have hone : ∀ e, LeafPreimage (onboardedBacking s) c 5 (s + 1) 0 e → e = ⟨5, s + 1, 0⟩ := by
    rintro e (he | he)
    · exact List.mem_singleton.mp he
    · exact he
  intro e e' he he' _
  rw [hone e he, hone e' he']

theorem onboardedSystem_wf (s : ℕ) : Wf (onboardedSystem s) := by
  refine ⟨fun _ => Reaches.refl, fun _ _ => Reaches.refl, ?_,
    fun _ _ => by norm_num [onboardedSystem, setup]⟩
  intro c i j hij
  show (if i ≤ s + 1 then 0 else 2) ≤ (if j ≤ s + 1 then 0 else 2)
  split_ifs <;> omega

theorem onboarded_rootEntriesPushed (s : ℕ) :
    RootEntriesPushed (onboardedPushes s) (onboardedBacking s) :=
  fun _ _ he => List.mem_singleton.mp he

theorem onboarded_clock (s : ℕ) : ClockFromPushes (onboardedSystem s) (onboardedPushes s) := by
  intro c e he
  have he' : e = ⟨5, s + 1, 0⟩ := he
  subst he'
  show (if s + 1 ≤ s + 1 then 0 else 2) = 0
  simp

theorem onboarded_aggregatesPushed (s : ℕ) :
    AggregatesPushed (onboardedPushes s) (onboardedBacking s) := by
  intro c e he _
  have he' : e = ⟨5, s + 1, 0⟩ := he
  subst he'
  exact List.mem_singleton_self _

theorem onboarded_gaps (s : ℕ) :
    GapsAfterRootLate (onboardedSystem s) (onboardedPushes s) (onboardedRoot s) := by
  intro c m hm _
  have hm' : s + 1 < m := hm
  show 1 < (if m ≤ s + 1 then 0 else 2)
  rw [ite_eq_right (by omega)]
  norm_num

theorem onboarded_entriesTimed (s : ℕ) : EntriesTimed (onboardedSystem s) (onboardedBacking s) :=
  entriesTimed_from_pushLog (onboarded_rootEntriesPushed s) (onboarded_clock s)

theorem onboarded_aggregates (s : ℕ) : Aggregates (onboardedSystem s) (onboardedRoot s) :=
  aggregates_from_pushLog (onboarded_aggregatesPushed s) (onboarded_clock s) (onboarded_gaps s)

theorem onboarded_timeout_witness : Properties.OnboardedTimeoutWitness := by
  intro s
  have h1 : (0 : UInt256) < 1 := by decide
  have habs : AbsenceAccepted demoHash 0 (fun _ => 0) ((onboardedSystem s).tree 0 (s + 1))
      ((onboardedSystem s).height 0 (s + 1)) 1
      ⟨⟨0, 0, 0⟩, 0, honestSibs demoHash 0 (leafHashes (fun _ => 0) setup) 0, 0⟩ :=
    setup_absence_accepted demoHash 0 (fun _ => 0) h1
  have hnab : ¬ AbsenceBreak demoHash 0 (fun _ => 0) (onboardedSystem s) 0 0 (s + 1)
      ⟨⟨0, 0, 0⟩, 0, honestSibs demoHash 0 (leafHashes (fun _ => 0) setup) 0, 0⟩ := by
    rintro (⟨hlate, _⟩ | ⟨_, hb⟩)
    · have h0 : (onboardedSystem s).time 0 (s + 1) = 0 := by simp [onboardedSystem]
      rw [h0] at hlate
      exact absurd hlate (lt_irrefl 0)
    · exact honest_proof_no_break demoHash 0 (fun _ => 0) setup 0 0 (by norm_num [setup]) hb
  refine ⟨demoHash, 0, fun _ => 0, fun _ _ => 1, onboardedSystem s, 0, rootLeaf,
    onboardedRoot s, onboardedBacking s, onboardedPushes s, ⟨0, [⟨0, 0⟩], 0⟩, ⟨0, 0⟩,
    ⟨⟨0, 0, 0⟩, 0, honestSibs demoHash 0 (leafHashes (fun _ => 0) setup) 0, 0⟩,
    honestSibs demoHash 0 [5] 0, 5, 0,
    onboardedSlot_reachable false s 5 0, rfl, onboardedSystem_wf s,
    onboarded_rootEntriesPushed s, onboarded_clock s, onboarded_aggregatesPushed s,
    onboarded_gaps s, onboarded_entriesNotEmpty, onboarded_pairInjOn, onboarded_leafInj s 0,
    ⟨0, by show 0 < 1; norm_num, by norm_num⟩, onboarded_endBranch s 0,
    Or.inr ⟨onboarded_endBranch s 0, habs⟩, hnab, ?_⟩
  intro n _ hmem
  exact not_mem_setup h1 hmem

/-- The composition at starting batch `s`, for the two named instances. -/
theorem onboarded_composes (s : ℕ) :
    EndBranchVerified (onboardedSystem s) (onboardedRoot s) 0 0 (s + 1)
      ∧ IsLastOnTime (onboardedSystem s) 0 0 (s + 1) := by
  have hv := positioned_endBranch_verified_on (onboarded_entriesTimed s) onboarded_entriesNotEmpty
    onboarded_pairInjOn (onboarded_leafInj s 0) (onboarded_endBranch s 0)
  exact ⟨hv, isLastOnTime_of_verified (onboarded_aggregates s) hv⟩

theorem onboarded_at_100_composes : Properties.OnboardedAt100Composes :=
  ⟨demoHash, 0, rootLeaf, onboardedRoot 100, onboardedBacking 100, onboardedSystem 100, 0, 0,
    honestSibs demoHash 0 [5] 0, 5, 0, onboardedSlot_reachable false 100 5 0, rfl, rfl, rfl,
    onboarded_endBranch 100 0, onboarded_entriesTimed 100, onboarded_aggregates 100,
    onboarded_entriesNotEmpty, onboarded_pairInjOn, onboarded_leafInj 100 0,
    (onboarded_composes 100).1, (onboarded_composes 100).2⟩

theorem eraVm_no_genesis_composes : Properties.EraVmNoGenesisComposes :=
  ⟨demoHash, 0, rootLeaf, onboardedRoot 0, onboardedBacking 0, onboardedSystem 0, 0, 0,
    honestSibs demoHash 0 [5] 0, 5, 0, onboardedSlot_reachable false 0 5 0, rfl, rfl, rfl,
    onboarded_endBranch 0 0, onboarded_entriesTimed 0, onboarded_aggregates 0,
    onboarded_entriesNotEmpty, onboarded_pairInjOn, onboarded_leafInj 0 0,
    (onboarded_composes 0).1, (onboarded_composes 0).2⟩

/-! ### A migration gap inside the tree -/

/-- Registered at `49`; batch `50` pushed; `setMigratingChainBatchNumber(80)`; batch `81`
pushed. -/
def gapSlot : ChainTreeSlot :=
  ⟨81, Function.update (Function.update (fun _ => false) 50 true) 81 true,
    [⟨5, 50, 0⟩, ⟨7, 81, 0⟩]⟩

theorem gapSlot_reachable : SlotReachable false 49 gapSlot := by
  have s1 : ChainTreeStep false (registeredSlot 49)
      ⟨50, Function.update (fun _ => false) 50 true, [⟨5, 50, 0⟩]⟩ :=
    ChainTreeStep.recordAndPush (registeredSlot 49) 50 5 0 rfl rfl
  have s2 : ChainTreeStep false ⟨50, Function.update (fun _ => false) 50 true, [⟨5, 50, 0⟩]⟩
      ⟨80, Function.update (fun _ => false) 50 true, [⟨5, 50, 0⟩]⟩ :=
    ChainTreeStep.migrate _ 80 (by show 50 ≤ 80; norm_num)
  have s3 : ChainTreeStep false ⟨80, Function.update (fun _ => false) 50 true, [⟨5, 50, 0⟩]⟩
      gapSlot :=
    ChainTreeStep.recordAndPush _ 81 7 0 (by decide) rfl
  exact Relation.ReflTransGen.tail (Relation.ReflTransGen.tail
    (Relation.ReflTransGen.single s1) s2) s3

theorem gap_leafInj (c : Chain) : BatchLeafInjOn rootLeaf (LeafPreimage gapBacking c 7 81 0) := by
  have htwo : ∀ e, LeafPreimage gapBacking c 7 81 0 e → e = ⟨5, 50, 0⟩ ∨ e = ⟨7, 81, 0⟩ := by
    rintro e (he | he)
    · have he' : e ∈ [(⟨5, 50, 0⟩ : BatchEntry), ⟨7, 81, 0⟩] := he
      simpa using he'
    · exact Or.inr he
  intro e e' he he' heq
  rcases htwo e he with rfl | rfl <;> rcases htwo e' he' with rfl | rfl <;>
    first | rfl | exact absurd heq (by decide)

theorem gap_endBranch (c : Chain) :
    PositionedEndBranchAccepted gapBacking c 0 1 (honestSibs demoHash 0 [5, 7] 1) 7 81 0 where
  rootAfterDeadline := by show 0 < 1; norm_num
  onTime := le_refl 0
  lastBatch :=
    { inRange := by show 1 < 2; norm_num
      authenticated := by
        show walkPure demoHash (honestSibs demoHash 0 [5, 7] 1) 0 2 1 7 = rootOf demoHash 0 [5, 7] 2
        decide
      zeroRightSiblings := by
        show ∀ l < 2, (1 / 2 ^ l) % 2 = 0 → honestSibs demoHash 0 [5, 7] 1 l = zeros demoHash 0 l
        decide }

theorem gap_entriesTimed : EntriesTimed (onboardedSystem 80) gapBacking := by
  intro c e he
  have he' : e ∈ [(⟨5, 50, 0⟩ : BatchEntry), ⟨7, 81, 0⟩] := he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
  rcases he' with rfl | rfl <;> simp [onboardedSystem]

theorem gap_aggregates : Aggregates (onboardedSystem 80) gapRoot := by
  intro c m hm
  show m ≤ 81
  by_contra hcon
  have h2 : (onboardedSystem 80).time c m = 2 := by
    show (if m ≤ 80 + 1 then 0 else 2) = 2
    rw [ite_eq_right (by omega)]
  have h1 : (onboardedSystem 80).time c m ≤ 1 := hm
  omega

theorem migration_gap_inside_tree_witness : Properties.MigrationGapInsideTreeWitness :=
  ⟨gapSlot, demoHash, 0, rootLeaf, gapRoot, gapBacking, onboardedSystem 80, 0, 0,
    honestSibs demoHash 0 [5, 7] 1, 7, 0, gapSlot_reachable, rfl, rfl, gap_endBranch 0,
    demo_entriesNotEmpty, demo_pairInjOn, gap_leafInj 0, ⟨1, by show 1 < 2; norm_num, by decide⟩,
    gap_entriesTimed, gap_aggregates,
    positioned_endBranch_verified_on gap_entriesTimed demo_entriesNotEmpty demo_pairInjOn
      (gap_leafInj 0) (gap_endBranch 0)⟩

/-! ## What is load-bearing -/

theorem positioned_conclusion_not_always : Properties.PositionedConclusionNotAlways := by
  refine ⟨demoHash, 0, rootLeaf, threeRoot, threeBacking, 0, 1,
    honestSibs demoHash 0 [5, 7, 9] 1, 7, 2, 0, by show 1 < 3; norm_num,
    honest_walk_root demoHash 0 [5, 7, 9] 2 1 (by norm_num), ?_⟩
  rintro (hs | hb | hc | ⟨hne, _⟩)
  · unfold SubmittedIsLastEntry at hs
    exact absurd hs (by decide)
  · exact demo_no_pinned_break hb
  · exact honest_walk_no_collision demoHash 0 [5, 7, 9] 2 1 hc
  · exact hne rfl

/-- The forged submission's tree: height 0, so the walk is the leaf for every node hash. -/
theorem flat_lastBatch (s : ℕ) (h : Hash) (c : Chain) (sibs : ℕ → UInt256) (N : ℕ) :
    PositionedLastBatchAccepted (flatOnboardedBacking s h) c 0 sibs 5 N 0 where
  inRange := by show 0 < 1; norm_num
  authenticated := rfl
  zeroRightSiblings := fun l hl => absurd hl (Nat.not_lt_zero l)

lemma deliveringSystem_wf {s : ℕ} {a : UInt256} (ha : 0 < a) : Wf (deliveringSystem s a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    show Reaches setup (if 0 ≤ s then setup else insert setup a 0)
    rw [ite_eq_left (Nat.zero_le s)]
    exact Reaches.refl
  · intro c n
    show Reaches (if n ≤ s then setup else insert setup a 0)
      (if n + 1 ≤ s then setup else insert setup a 0)
    by_cases h1 : n + 1 ≤ s
    · rw [ite_eq_left (show n ≤ s by omega), ite_eq_left h1]
      exact Reaches.refl
    · by_cases h2 : n ≤ s
      · rw [ite_eq_left h2, ite_eq_right h1]
        exact Reaches.tail Reaches.refl (setup_insertGuard ha)
      · rw [ite_eq_right h2, ite_eq_right h1]
        exact Reaches.refl
  · intro c i j hij
    show (if i ≤ s + 1 then 0 else 2) ≤ (if j ≤ s + 1 then 0 else 2)
    split_ifs <;> omega
  · intro c n
    show (if n ≤ s then setup else insert setup a 0).leafCount ≤ 2 ^ (if n ≤ s then 0 else 1)
    by_cases h1 : n ≤ s
    · rw [ite_eq_left h1, ite_eq_left h1]
      norm_num [setup]
    · rw [ite_eq_right h1, ite_eq_right h1, insertSetup_leafCount]
      norm_num

theorem batch_number_forgery_locates_leaf_clash :
    Properties.BatchNumberForgeryLocatesLeafClash := by
  intro h z0 hl a ha
  have htree0 : (deliveringSystem 100 a).tree 0 0 = setup := by simp [deliveringSystem]
  have hheight0 : (deliveringSystem 100 a).height 0 0 = 0 := by simp [deliveringSystem]
  have htime0 : (deliveringSystem 100 a).time 0 0 = 0 := by simp [deliveringSystem]
  have hend : PositionedEndBranchAccepted (flatOnboardedBacking 100 h) 0 0 0 (fun _ => 0) 5 0 0 :=
    ⟨by show 0 < 1; norm_num, le_refl 0, flat_lastBatch 100 h 0 (fun _ => 0) 0⟩
  have habs : AbsenceAccepted h z0 hl ((deliveringSystem 100 a).tree 0 0)
      ((deliveringSystem 100 a).height 0 0) a
      ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩ := by
    rw [htree0, hheight0]
    exact setup_absence_accepted h z0 hl ha
  refine ⟨fun _ _ => a, ⟨0, [⟨0, 0⟩], 0⟩, ⟨0, 0⟩,
    ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩, fun _ => 0,
    deliveringSystem_wf ha, ?_, ?_, Or.inr ⟨hend, habs⟩, ?_, ?_, ?_, ?_, ?_⟩
  · -- `Aggregates`: every batch after 101 settles at time 2
    intro c m hm
    show m ≤ 101
    by_contra hcon
    have h2 : (deliveringSystem 100 a).time c m = 2 := by
      show (if m ≤ 100 + 1 then 0 else 2) = 2
      rw [ite_eq_right (by omega)]
    have h1 : (deliveringSystem 100 a).time c m ≤ 1 := hm
    omega
  · -- `EntriesTimed`: batch 101 settled at time 0
    intro c e he
    have he' : e = ⟨5, 101, 0⟩ := List.mem_singleton.mp he
    subst he'
    simp [deliveringSystem]
  · -- the leg was committed during batch 101, which settled on time
    intro hall
    refine hall 101 (by simp [deliveringSystem]) ?_
    have ht : (deliveringSystem 100 a).tree 0 101 = insert setup a 0 := by simp [deliveringSystem]
    show a ∈ keys (toAbs ((deliveringSystem 100 a).tree 0 101))
    rw [ht]
    exact mem_insertSetup ha
  · -- the absence proof against batch 0's empty tree is honest
    rintro (⟨hlate, _⟩ | ⟨_, hb⟩)
    · rw [htime0] at hlate
      exact absurd hlate (lt_irrefl 0)
    · unfold ImtProofBreak at hb
      rw [htree0, hheight0] at hb
      exact honest_proof_no_break h z0 hl setup 0 0 (by norm_num [setup]) hb
  · exact no_pinned_break_at_end h 0 _ 0 (by show 1 ≤ 0 + 1; norm_num)
  · rintro ⟨i, hi, _⟩
    exact absurd hi (Nat.not_lt_zero i)
  · refine ⟨?_, rfl⟩
    show (⟨5, 101, 0⟩ : BatchEntry) ≠ ⟨5, 0, 0⟩
    decide

theorem migration_gap_is_load_bearing : Properties.MigrationGapIsLoadBearing := by
  intro h z0 hl a ha
  have hend : PositionedEndBranchAccepted (staleBacking h) 0 0 0 (fun _ => 0) 5 0 0 :=
    ⟨by show 0 < 1; norm_num, le_refl 0,
      ⟨by show 0 < 1; norm_num, rfl, fun l hl => absurd hl (Nat.not_lt_zero l)⟩⟩
  have habs : AbsenceAccepted h z0 hl ((staleSystem a).tree 0 0) ((staleSystem a).height 0 0) a
      ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩ := by
    rw [staleSystem_tree_zero, staleSystem_height_zero]
    exact setup_absence_accepted h z0 hl ha
  refine ⟨fun _ _ => a, ⟨0, [⟨0, 0⟩], 0⟩, ⟨0, 0⟩,
    ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩, fun _ => 0,
    staleSystem_wf ha, ?_, ?_, ?_, ?_, Or.inr ⟨hend, habs⟩, ?_, ?_, ?_, ?_⟩
  · intro c e he
    exact List.mem_singleton.mp he
  · intro c e he
    have he' : e = ⟨5, 0, 0⟩ := he
    subst he'
    rfl
  · intro c e he _
    have he' : e = ⟨5, 0, 0⟩ := he
    subst he'
    exact List.mem_singleton_self _
  · -- batch 1 was never pushed here, yet it settled at time 0, before the root
    intro hgap
    have := hgap 0 1 (by show 0 < 1; norm_num)
      (fun e he => by
        have he' : e = ⟨5, 0, 0⟩ := he
        subst he'
        decide)
    exact absurd this (by simp [staleRoot])
  · rintro (hpb | ⟨i, hi, _⟩ | ⟨hne, _⟩)
    · exact no_pinned_break_at_end h 0 _ 0 (by show 1 ≤ 0 + 1; norm_num) hpb
    · exact absurd hi (Nat.not_lt_zero i)
    · exact hne rfl
  · rintro (⟨hlate, _⟩ | ⟨_, hb⟩)
    · exact absurd hlate (by simp)
    · unfold ImtProofBreak at hb
      rw [staleSystem_tree_zero, staleSystem_height_zero] at hb
      exact honest_proof_no_break h z0 hl setup 0 0 (by norm_num [setup]) hb
  · simp
  · show a ∈ keys (toAbs ((staleSystem a).tree 0 1))
    rw [staleSystem_tree_succ]
    exact mem_insertSetup ha

end Contracts.BatchPosition

/-! ## Certificates -/

namespace Contracts.BatchPosition

theorem CurrentCompositionCannotRepresentOnboardingAt100 :
    Properties.CurrentCompositionCannotRepresentOnboardingAt100 :=
  current_composition_cannot_represent_onboarding_at_100
theorem ReachableSlotNumbersIncrease : Properties.ReachableSlotNumbersIncrease :=
  fun _ _ _ hr => reachable_slot_numbers_increase hr
theorem TreeAboveStartWithoutGenesis : Properties.TreeAboveStartWithoutGenesis :=
  fun _ _ _ hr hng => tree_above_start_without_genesis hr hng
theorem TreePositionBelowBatchNumber : Properties.TreePositionBelowBatchNumber :=
  fun _ _ _ hr hng => tree_position_below_batch_number hr hng
theorem ReachableSlotsBackARoot : Properties.ReachableSlotsBackARoot :=
  reachable_slots_back_a_root
theorem EntryNumbersBoundedByUpTo : Properties.EntryNumbersBoundedByUpTo :=
  fun _ _ _ _ B c => entry_le_upTo B c
theorem LastPositionFixesBatchNumber : Properties.LastPositionFixesBatchNumber :=
  fun _ _ _ _ B c _ _ _ _ hlast hleaf => last_position_fixes_batch_number B c hlast hleaf
theorem SubmittedLastEntryIsUpTo : Properties.SubmittedLastEntryIsUpTo :=
  fun _ _ _ _ _ _ _ _ _ hs => submitted_last_is_upTo hs
theorem SubmittedLastEntryTimed : Properties.SubmittedLastEntryTimed :=
  fun _ _ _ _ _ _ _ _ _ _ hT hs => submitted_last_timed hT hs
theorem MaskBoundGivesOccupiedRange : Properties.MaskBoundGivesOccupiedRange :=
  fun _ _ _ _ B c _ _ _ _ _ hmask hw => mask_bound_gives_occupied_range B c hmask hw
theorem PositionedLastBatchIdentifiesLastEntryPinned :
    Properties.PositionedLastBatchIdentifiesLastEntryPinned :=
  fun _ _ _ _ _ _ _ _ _ _ _ ha => positioned_lastBatch_pinned ha
theorem NoPositionedEndBreakOn : Properties.NoPositionedEndBreakOn :=
  fun _ _ _ _ _ _ _ _ _ _ _ hpos hsep hinj hleaf => no_positioned_end_break_on hpos hsep hinj hleaf
theorem PositionedLastBatchIdentifiesLastBatchOn :
    Properties.PositionedLastBatchIdentifiesLastBatchOn :=
  fun _ _ _ _ _ _ _ _ _ _ _ hsep hinj hleaf ha => positioned_lastBatch_on hsep hinj hleaf ha
theorem PositionedEndBranchImpliesVerifiedPinned :
    Properties.PositionedEndBranchImpliesVerifiedPinned :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hT ha => positioned_endBranch_verified_pinned hT ha
theorem PositionedEndBranchImpliesVerifiedOn : Properties.PositionedEndBranchImpliesVerifiedOn :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hT hsep hinj hleaf ha =>
    positioned_endBranch_verified_on hT hsep hinj hleaf ha
theorem PositionedAcceptedImpliesRefundablePinned :
    Properties.PositionedAcceptedImpliesRefundablePinned :=
  fun _ _ _ _ _ _ _ _ _ hagg hT _ _ _ _ _ _ _ _ ha =>
    positioned_accepted_implies_refundable_pinned hagg hT ha
theorem PositionedAcceptedImpliesRefundableOn : Properties.PositionedAcceptedImpliesRefundableOn :=
  fun _ _ _ _ _ _ _ _ _ hagg hT _ _ _ _ _ _ _ _ hsep hinj hleaf ha =>
    positioned_accepted_implies_refundable_on hagg hT hsep hinj hleaf ha
theorem PositionedTimeoutMeansMissedDeadlineOrBreak :
    Properties.PositionedTimeoutMeansMissedDeadlineOrBreak :=
  fun _ _ _ _ _ hS _ _ _ _ hagg hT _ _ _ _ _ _ _ _ ha =>
    positioned_timeout_means_missed_deadline_or_break hS hagg hT ha
theorem AggregatesFromPushLog : Properties.AggregatesFromPushLog :=
  fun _ _ _ _ _ _ _ hpush hclk hgap => aggregates_from_pushLog hpush hclk hgap
theorem EntriesTimedFromPushLog : Properties.EntriesTimedFromPushLog :=
  fun _ _ _ _ _ _ _ hroot hclk => entriesTimed_from_pushLog hroot hclk
theorem PushLogTimeoutMeansMissedDeadlineOrBreak :
    Properties.PushLogTimeoutMeansMissedDeadlineOrBreak :=
  fun _ _ _ _ _ hS _ _ _ _ _ hroot hclk hpush hgap _ _ _ _ _ _ _ _ ha =>
    positioned_timeout_means_missed_deadline_or_break hS (aggregates_from_pushLog hpush hclk hgap)
      (entriesTimed_from_pushLog hroot hclk) ha
theorem OnboardedTimeoutWitness : Properties.OnboardedTimeoutWitness := onboarded_timeout_witness
theorem OnboardedAt100Composes : Properties.OnboardedAt100Composes := onboarded_at_100_composes
theorem EraVmNoGenesisComposes : Properties.EraVmNoGenesisComposes := eraVm_no_genesis_composes
theorem MigrationGapInsideTreeWitness : Properties.MigrationGapInsideTreeWitness :=
  migration_gap_inside_tree_witness
theorem PositionedConclusionNotAlways : Properties.PositionedConclusionNotAlways :=
  positioned_conclusion_not_always
theorem BatchNumberForgeryLocatesLeafClash : Properties.BatchNumberForgeryLocatesLeafClash :=
  batch_number_forgery_locates_leaf_clash
theorem MigrationGapIsLoadBearing : Properties.MigrationGapIsLoadBearing :=
  migration_gap_is_load_bearing

end Contracts.BatchPosition
