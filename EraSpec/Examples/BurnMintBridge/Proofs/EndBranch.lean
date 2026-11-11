import EraSpec.Examples.BurnMintBridge.Properties.EndBranch
import EraSpec.Contracts.AtomicInteropProof.Proofs.TimeoutSoundness
import EraSpec.Contracts.AtomicInteropProof.Proofs.LastBatchInRoot
import EraSpec.Protocol.InteropAtomicity.Proofs.Timeout

/-!
# Proofs: the END timeout branch composed into the reference bridge

The END branch is used through the existing theorems rather than re-proved:
`TimeoutSoundness.timeout_implies_never_finalized` (§1),
`TimeoutSoundness.begin_absence_implies_never_finalized` and
`LastBatchInRoot.end_branch_from_onchain_check` (§2), and
`Contracts.Timeout.LastBatchProofIdentifiesLastBatchPinned` (§3).  The bridge-level results
go through `ProtocolComposition`'s own `prepared_bridge_no_double_payment` and
`prepared_bridge_value_conserved`, by embedding the new runs into the adapter's runs.
-/

namespace Applications.BurnMintBridge.EndBranch

open IMTAbstract Properties.PreparedBridge

/-! ## Valid histories -/

theorem valid_sound0 {H : History} (hH : H.Valid) (c : UInt256) : SoundState (H.tree c 0) := by
  rw [hH.genesis c]
  exact genesis_soundState

theorem valid_evolution {H : History} (hH : H.Valid) (c : UInt256) : Evolution (H.tree c) :=
  guardedEvolution_isEvolution (hH.guarded c) (valid_sound0 hH c)

theorem valid_keys_mono {H : History} (hH : H.Valid) (c : UInt256) {m n : ℕ} (hmn : m ≤ n) :
    keys (H.tree c m) ⊆ keys (H.tree c n) :=
  evolution_keys_mono (valid_evolution hH c) hmn

theorem valid_gapSound {H : History} (hH : H.Valid) (c : UInt256) (n : ℕ) :
    GapSound (H.tree c n) :=
  (guardedEvolution_sound (hH.guarded c) (valid_sound0 hH c) n).1

/-- A gap witness in a snapshot excludes the value from that snapshot. -/
theorem absent_of_gap {H : History} (hH : H.Valid) {c : UInt256} {n : ℕ} {v : UInt256}
    (hgap : GapWitness (H.tree c n) v) : v ∉ keys (H.tree c n) := fun hmem =>
  present_not_reclaimable (valid_gapSound hH c n) hmem hgap

/-- An absent value has a gap witness (reclaim liveness).  For `v = 0` the premise is false:
the genesis sentinel key is in every snapshot. -/
theorem gap_of_absent {H : History} (hH : H.Valid) {c : UInt256} {n : ℕ} {v : UInt256}
    (habs : v ∉ keys (H.tree c n)) : GapWitness (H.tree c n) v := by
  by_cases hv : v = 0
  · subst hv
    exfalso
    apply habs
    apply valid_keys_mono hH c (Nat.zero_le n)
    rw [hH.genesis c]
    exact genesis_zero_mem
  · exact (guardedEvolution_reclaimable_iff_absent (hH.guarded c) (hH.genesis c) hv).mpr habs

theorem batchHistory_appendOnly {H : History} (hH : H.Valid) (c : UInt256) :
    AttackVectors.TimeoutSoundness.AppendOnly (batchHistory H c) :=
  fun n => valid_keys_mono hH c (Nat.le_succ n)

theorem batchHistory_timeOrdered {H : History} (hH : H.Valid) (c : UInt256) :
    AttackVectors.TimeoutSoundness.TimeOrdered (batchHistory H c) :=
  fun _ _ hab => hH.monotone_time c hab

/-! ## Runs -/

theorem run_monotone {E E' : Evidence} (hf : ∀ i, E.finalize i → E'.finalize i)
    (hr : ∀ i, E.recover i → E'.recover i) {s t : State} (h : Run E s t) : Run E' s t := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    refine .tail ih ?_
    cases hstep with
    | prepare hp => exact .prepare hp
    | interfere hi => exact .interfere hi
    | execute hc he => exact .execute (hf _ hc) he
    | recover hc hrec => exact .recover (hr _ hc) hrec

/-- One step, with no evidence soundness: it conserves value unless its target has paid both
outcomes. -/
theorem step_conserves_unless_double {E : Evidence} {s t : State} (hstep : Step E s t)
    (hnot : ¬ (t.delivered = true ∧ t.refunded = true)) : accounted t = accounted s := by
  cases hstep with
  | prepare hp =>
    rcases hp with ⟨hrecord, hd, hr, _, hbalance, rfl⟩
    simp only [accounted, limbo, burn, hd, hr, hrecord]
    simp
    omega
  | interfere hi =>
    cases hi with
    | source hb =>
      change (s.sourceBalance - _ + s.destinationBalance + (s.spent + _) + limbo s) = _
      unfold accounted
      omega
    | destination hb =>
      change (s.sourceBalance + (s.destinationBalance - _) + (s.spent + _) + limbo s) = _
      unfold accounted
      omega
  | execute _ he =>
    rcases he with ⟨⟨hrecord, hd⟩, _, rfl⟩
    cases hr : s.refunded with
    | true => exact absurd ⟨rfl, hr⟩ hnot
    | false =>
      simp [accounted, limbo, mint, hd, hr, hrecord]
      omega
  | recover _ he =>
    rcases he with ⟨hrecord, hr, rfl⟩
    cases hd : s.delivered with
    | true => exact absurd ⟨hd, rfl⟩ hnot
    | false =>
      simp [accounted, limbo, restore, hd, hr, hrecord]
      omega

theorem run_conserves_unless_double {E : Evidence} {s t : State} (h : Run E s t)
    (hnot : ¬ (t.delivered = true ∧ t.refunded = true)) : accounted t = accounted s := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    have hflags := step_flags_persist hstep
    have hmid : ¬ (_ ∧ _) := fun hboth => hnot ⟨hflags.1 hboth.1, hflags.2 hboth.2⟩
    exact (step_conserves_unless_double hstep hnot).trans (ih hmid)

/-- **WITHOUT SOUNDNESS, ONLY DOUBLE PAYMENT BREAKS CONSERVATION.** -/
theorem value_conserved_unless_double_paid {E : Evidence} {source destination : ℕ} {s : State}
    (h : Run E (initial source destination) s) :
    (s.delivered = true ∧ s.refunded = true) ∨ accounted s = source + destination := by
  by_cases hboth : s.delivered = true ∧ s.refunded = true
  · exact Or.inl hboth
  · refine Or.inr ?_
    rw [run_conserves_unless_double h hboth]
    simp [accounted, limbo, initial]

/-! ## 1. The END branch over the adapter's history -/

/-- **THE ABSTRACT END FORM IS ALREADY A SUCCESSOR-PINNED `Missing`.** -/
theorem missingEnd_implies_missing {H : History} {l : Leg} (h : MissingEnd H l) :
    Missing H l := by
  obtain ⟨B, T, _, hDT, hlast, W, hW, hlow, hwin⟩ := h
  exact ⟨B, W, lt_of_lt_of_le hDT (hlast (B + 1) (Nat.lt_succ_self B)), hW, hlow, hwin⟩

theorem missingEither_iff_missing {H : History} {l : Leg} : MissingEither H l ↔ Missing H l :=
  ⟨fun h => h.elim id missingEnd_implies_missing, Or.inl⟩

theorem missingEnd_iff_absence {H : History} (hH : H.Valid) {l : Leg} :
    MissingEnd H l ↔ ∃ (B : ℕ) (T : UInt256),
      H.settledAt l.sourceChain B ≤ l.deadline ∧ l.deadline < T ∧
        (∀ n, B < n → T ≤ H.settledAt l.sourceChain n) ∧
        l.commitValue ∉ keys (H.tree l.sourceChain B) := by
  constructor
  · rintro ⟨B, T, hon, hDT, hlast, hgap⟩
    exact ⟨B, T, hon, hDT, hlast, absent_of_gap hH hgap⟩
  · rintro ⟨B, T, hon, hDT, hlast, habs⟩
    exact ⟨B, T, hon, hDT, hlast, gap_of_absent hH habs⟩

/-- **EITHER BRANCH MEANS NEVER FINALIZED**, through
`TimeoutSoundness.timeout_implies_never_finalized` on the leg's chain. -/
theorem missingEither_never_finalized {H : History} (hH : H.Valid) {l : Leg}
    (hm : MissingEither H l) (n : ℕ) (hn : H.settledAt l.sourceChain n ≤ l.deadline) :
    l.commitValue ∉ keys (H.tree l.sourceChain n) := by
  have hbranch : (∃ L, l.deadline.val < (batchHistory H l.sourceChain).time L ∧
        l.commitValue ∉ AttackVectors.TimeoutSoundness.beginSet (batchHistory H l.sourceChain) L)
      ∨ (∃ B T, (batchHistory H l.sourceChain).time B ≤ l.deadline.val ∧
          l.deadline.val < T ∧ (∀ n, B < n → T ≤ (batchHistory H l.sourceChain).time n) ∧
          l.commitValue ∉ (batchHistory H l.sourceChain).endSet B) := by
    rcases hm with ⟨m, W, hlate, hW, hlow, hwin⟩ | ⟨B, T, hon, hDT, hlast, hgap⟩
    · exact Or.inl ⟨m + 1, hlate, absent_of_gap hH ⟨W, hW, hlow, hwin⟩⟩
    · exact Or.inr ⟨B, T.val, hon, hDT, fun n hn => hlast n hn, absent_of_gap hH hgap⟩
  exact AttackVectors.TimeoutSoundness.timeout_implies_never_finalized
    (batchHistory_appendOnly hH _) (batchHistory_timeOrdered hH _) hbranch n hn

theorem onTime_excludes_missingEither {H : History} (hH : H.Valid) {l : Leg}
    (hon : OnTime H l) : ¬ MissingEither H l := by
  intro hm
  obtain ⟨n, hn, hmem⟩ := hon
  exact missingEither_never_finalized hH hm n hn hmem

theorem evidenceEither_sound {H : History} (hH : H.Valid) (flow : Transfer → List Leg) :
    (evidenceEither H flow).Sound := by
  intro i
  rintro ⟨hall, l, hl, hm⟩
  exact onTime_excludes_missingEither hH (hall l hl) hm

theorem evidenceEither_runs_iff {H : History} {flow : Transfer → List Leg} {s t : State} :
    Run (evidenceEither H flow) s t ↔ Run (evidence H flow) s t := by
  constructor
  · refine run_monotone (E := evidenceEither H flow) (E' := evidence H flow) (fun _ h => h) ?_
    rintro i ⟨l, hl, hm⟩
    exact ⟨l, hl, missingEither_iff_missing.mp hm⟩
  · refine run_monotone (E := evidence H flow) (E' := evidenceEither H flow) (fun _ h => h) ?_
    rintro i ⟨l, hl, hm⟩
    exact ⟨l, hl, Or.inl hm⟩

/-! ## 2. The timeout gate as the contract runs it -/

/-- **THE ZERO-CASCADE CHECK IS EXACTLY "LAST IN ROOT".** -/
theorem endVia_iff_endLastVia {H : History} {R : Contracts.Timeout.SlRoot} {l : Leg} :
    EndVia H R l ↔ EndLastVia H R l := by
  constructor
  · rintro ⟨hroot, B, depth, hon, hin, hcap, hemp, hgap⟩
    have hlast := AttackVectors.LastBatchInRoot.last_of_rightEmpty hin hcap hemp
    have hB : B = R.upTo l.sourceChain := by
      change R.upTo l.sourceChain + 1 = B + 1 at hlast
      omega
    subst hB
    exact ⟨hroot, hon, hgap⟩
  · rintro ⟨hroot, hon, hgap⟩
    exact ⟨hroot, R.upTo l.sourceChain, R.upTo l.sourceChain + 1, hon, Nat.lt_succ_self _,
      (Nat.lt_two_pow_self).le, AttackVectors.LastBatchInRoot.rightEmpty_of_last, hgap⟩

/-- **A BEGIN-BRANCH TIMEOUT MEANS NEVER FINALIZED**, via
`TimeoutSoundness.begin_absence_implies_never_finalized`; no settlement-layer premise. -/
theorem beginVia_never_finalized {H : History} {R : Contracts.Timeout.SlRoot} (hH : H.Valid)
    {l : Leg} (hb : BeginVia H R l) (n : ℕ) (hn : H.settledAt l.sourceChain n ≤ l.deadline) :
    l.commitValue ∉ keys (H.tree l.sourceChain n) := by
  obtain ⟨_, L, _, hlate, hgap⟩ := hb
  have habs : l.commitValue
      ∉ AttackVectors.TimeoutSoundness.beginSet (batchHistory H l.sourceChain) L := by
    cases L with
    | zero => simp [AttackVectors.TimeoutSoundness.beginSet]
    | succ m => exact absent_of_gap hH hgap
  exact AttackVectors.TimeoutSoundness.begin_absence_implies_never_finalized
    (H := batchHistory H l.sourceChain) (D := l.deadline.val)
    (batchHistory_appendOnly hH _) (batchHistory_timeOrdered hH _) hlate habs n hn

/-- `RootAggregates` puts every batch outside root `R` after `R`'s creation:
`LastBatchInRoot.OutsideRootLate` for the root's `upTo + 1` batch leaves. -/
theorem outsideRootLate_of_aggregates {H : History} {R : Contracts.Timeout.SlRoot}
    (hagg : RootAggregates H R) (c : UInt256) :
    AttackVectors.LastBatchInRoot.OutsideRootLate (· < R.upTo c + 1)
      (batchHistory H c).time R.created := by
  intro m hm
  by_contra hlt
  have hin := hagg c m (le_of_lt (not_le.mp hlt))
  exact hm (Nat.lt_succ_of_le hin)

/-- **AN END-BRANCH TIMEOUT MEANS NEVER FINALIZED**, via
`LastBatchInRoot.end_branch_from_onchain_check`. -/
theorem endVia_never_finalized {H : History} {R : Contracts.Timeout.SlRoot} (hH : H.Valid)
    (hagg : RootAggregates H R) {l : Leg} (he : EndVia H R l) (n : ℕ)
    (hn : H.settledAt l.sourceChain n ≤ l.deadline) :
    l.commitValue ∉ keys (H.tree l.sourceChain n) := by
  obtain ⟨hroot, B, depth, _, hin, hcap, hemp, hgap⟩ := he
  exact AttackVectors.LastBatchInRoot.end_branch_from_onchain_check
    (H := batchHistory H l.sourceChain) (time := (batchHistory H l.sourceChain).time)
    (D := l.deadline.val) (batchHistory_appendOnly hH _) rfl hroot hin hcap hemp
    (outsideRootLate_of_aggregates hagg l.sourceChain) (absent_of_gap hH hgap) n hn

theorem timeoutVia_never_finalized {H : History} {R : Contracts.Timeout.SlRoot} (hH : H.Valid)
    (hagg : RootAggregates H R) {l : Leg} (ht : TimeoutVia H R l) (n : ℕ)
    (hn : H.settledAt l.sourceChain n ≤ l.deadline) :
    l.commitValue ∉ keys (H.tree l.sourceChain n) :=
  ht.elim (fun hb => beginVia_never_finalized hH hb n hn)
    (fun he => endVia_never_finalized hH hagg he n hn)

/-- The batch after an aggregating root's last batch settled after the root, hence after the
deadline. -/
theorem next_after_root_late {H : History} {R : Contracts.Timeout.SlRoot}
    (hagg : RootAggregates H R) {c D : UInt256} (hroot : D.val < R.created) :
    D < H.settledAt c (R.upTo c + 1) := by
  show D.val < (H.settledAt c (R.upTo c + 1)).val
  by_contra hle
  have hin := hagg c (R.upTo c + 1) (le_trans (not_lt.mp hle) (le_of_lt hroot))
  omega

/-- **THE GATE AS RUN REFINES THE ADAPTER.** -/
theorem timeoutVia_implies_missing {H : History} {R : Contracts.Timeout.SlRoot} (hH : H.Valid)
    (hagg : RootAggregates H R) {l : Leg} (ht : TimeoutVia H R l) : Missing H l := by
  rcases ht with ⟨_, L, _, hlate, hgap⟩ | he
  · cases L with
    | zero =>
      -- batch 0 begins at the genesis snapshot, and batch 1 is at least as late as batch 0
      obtain ⟨W, hW, hlow, hwin⟩ := hgap
      refine ⟨0, W, lt_of_lt_of_le hlate (hH.monotone_time l.sourceChain (Nat.zero_le 1)),
        ?_, hlow, hwin⟩
      rw [hH.genesis l.sourceChain]
      exact hW
    | succ m =>
      obtain ⟨W, hW, hlow, hwin⟩ := hgap
      exact ⟨m, W, hlate, hW, hlow, hwin⟩
  · obtain ⟨hroot, _, W, hW, hlow, hwin⟩ := endVia_iff_endLastVia.mp he
    exact ⟨R.upTo l.sourceChain, W, next_after_root_late hagg hroot, hW, hlow, hwin⟩

theorem checkedEvidence_sound {H : History} {roots : Roots} (hH : H.Valid)
    (hagg : ∀ k, RootAggregates H (roots k)) (flow : Transfer → List Leg) :
    (checkedEvidence H roots flow).Sound := by
  intro i
  rintro ⟨hall, l, hl, k, ht⟩
  obtain ⟨n, hn, hmem⟩ := hall l hl
  exact timeoutVia_never_finalized hH (hagg k) ht n hn hmem

/-- Every run of the as-run bridge is a run of the adapter's bridge. -/
theorem checked_runs_are_adapter_runs {H : History} {roots : Roots} (hH : H.Valid)
    (hagg : ∀ k, RootAggregates H (roots k)) {flow : Transfer → List Leg} {s t : State}
    (h : Run (checkedEvidence H roots flow) s t) : Run (evidence H flow) s t := by
  refine run_monotone (E := checkedEvidence H roots flow) (E' := evidence H flow)
    (fun _ h => h) ?_ h
  rintro i ⟨l, hl, k, ht⟩
  exact ⟨l, hl, timeoutVia_implies_missing hH (hagg k) ht⟩

theorem checked_bridge_no_double_payment {H : History} {roots : Roots} (hH : H.Valid)
    (hagg : ∀ k, RootAggregates H (roots k)) (flow : Transfer → List Leg)
    {source destination : ℕ} {s : State}
    (hrun : Run (checkedEvidence H roots flow) (initial source destination) s) :
    ¬ (s.delivered = true ∧ s.refunded = true) :=
  prepared_bridge_no_double_payment hH flow (checked_runs_are_adapter_runs hH hagg hrun)

theorem checked_bridge_value_conserved {H : History} {roots : Roots} (hH : H.Valid)
    (hagg : ∀ k, RootAggregates H (roots k)) (flow : Transfer → List Leg)
    {source destination : ℕ} {s : State}
    (hrun : Run (checkedEvidence H roots flow) (initial source destination) s) :
    accounted s = source + destination :=
  prepared_bridge_value_conserved hH flow (checked_runs_are_adapter_runs hH hagg hrun)

/-- **COMPLETENESS.**  The first late batch inside the root on the BEGIN branch; otherwise the
root's last batch, which is then in time, on the END branch. -/
theorem timeout_complete {H : History} (hH : H.Valid) {l : Leg} (hv : l.commitValue ≠ 0)
    (hnever : ∀ n, H.settledAt l.sourceChain n ≤ l.deadline →
      l.commitValue ∉ keys (H.tree l.sourceChain n))
    (R : Contracts.Timeout.SlRoot) (hroot : l.deadline.val < R.created) :
    TimeoutVia H R l := by
  classical
  by_cases hlate : ∃ L, L ≤ R.upTo l.sourceChain ∧ l.deadline < H.settledAt l.sourceChain L
  · obtain ⟨L, hLin, hLlate⟩ := hlate
    have hex : ∃ L, l.deadline < H.settledAt l.sourceChain L := ⟨L, hLlate⟩
    have hle : Nat.find hex ≤ L := Nat.find_min' hex hLlate
    have hspec : l.deadline < H.settledAt l.sourceChain (Nat.find hex) := Nat.find_spec hex
    have hmin : ∀ m < Nat.find hex, ¬ l.deadline < H.settledAt l.sourceChain m :=
      fun m hm => Nat.find_min hex hm
    generalize Nat.find hex = L₀ at hle hspec hmin
    refine Or.inl ⟨hroot, L₀, le_trans hle hLin, hspec, ?_⟩
    cases L₀ with
    | zero =>
      exact ⟨⟨0, 0⟩, Finset.mem_singleton_self _, Fin.pos_iff_ne_zero.mpr hv, Or.inl rfl⟩
    | succ m =>
      exact gap_of_absent hH (hnever m (not_lt.mp (hmin m (Nat.lt_succ_self m))))
  · have hon : H.settledAt l.sourceChain (R.upTo l.sourceChain) ≤ l.deadline :=
      not_lt.mp fun h => hlate ⟨R.upTo l.sourceChain, le_refl _, h⟩
    exact Or.inr (endVia_iff_endLastVia.mpr ⟨hroot, hon, gap_of_absent hH (hnever _ hon)⟩)

/-- **REFUND LIVENESS** at the bridge: one recovery step. -/
theorem timedOut_transfer_refund_enabled {H : History} {roots : Roots}
    {flow : Transfer → List Leg} (hH : H.Valid) {i : Transfer} {l : Leg} (hl : l ∈ flow i)
    (hv : l.commitValue ≠ 0)
    (hnever : ∀ n, H.settledAt l.sourceChain n ≤ l.deadline →
      l.commitValue ∉ keys (H.tree l.sourceChain n))
    {k : ℕ} (hroot : l.deadline.val < (roots k).created) {s : State}
    (hrec : s.record = some i) (hr : s.refunded = false) :
    ∃ t, Step (checkedEvidence H roots flow) s t ∧ t.refunded = true ∧
      t.sourceBalance = s.sourceBalance + i.amount :=
  ⟨restore s i, .recover ⟨l, hl, k, timeout_complete hH hv hnever (roots k) hroot⟩
    ⟨hrec, hr, rfl⟩, rfl, rfl⟩

/-! ## 3. The END branch with the hash-level last-batch proof -/

/-- **AN ACCEPTED END SUBMISSION FOR A LEG COMMITTED ON TIME IS A LOCATED BREAK.**  Through
`Contracts.Timeout.LastBatchProofIdentifiesLastBatchPinned`: the submitted batch is the root's
last, which the END branch's soundness excludes, or the break is on the submission. -/
theorem acceptedEnd_onTime_locates_break {h : MerkleSpec.Hash} {ze : UInt256} {H : History}
    {roots : Roots} {bk : Backing h ze roots} (hH : H.Valid)
    (hagg : ∀ k, RootAggregates H (roots k)) {e : EndSubmission} (hon : OnTime H e.leg)
    (ha : EndAcceptedBy H roots bk e) : EndBreak bk e := by
  obtain ⟨hroot, hintime, hlb, hgap⟩ := ha
  rcases Contracts.Timeout.LastBatchProofIdentifiesLastBatchPinned h ze (roots e.root)
      (bk e.root) e.leg.sourceChain e.batch e.sibs e.leaf hlb with hlast | hbreak
  · exfalso
    have hend : EndLastVia H (roots e.root) e.leg := by
      refine ⟨hroot, ?_, ?_⟩
      · rw [← hlast]
        exact hintime
      · rw [← hlast]
        exact hgap
    obtain ⟨n, hn, hmem⟩ := hon
    exact endVia_never_finalized hH (hagg e.root) (endVia_iff_endLastVia.mpr hend) n hn hmem
  · exact hbreak

/-- A double payment of the pinned bridge is authorized, on the refund side, by the recorded
transfer's END submission, and that submission carries a break. -/
theorem pinned_double_payment_locates_break {h : MerkleSpec.Hash} {ze : UInt256} {H : History}
    {roots : Roots} {bk : Backing h ze roots} (hH : H.Valid)
    (hagg : ∀ k, RootAggregates H (roots k)) {flow : Transfer → List Leg}
    {sub : Transfer → EndSubmission} {source destination : ℕ} {s : State}
    (hrun : Run (pinnedEvidence H roots bk flow sub) (initial source destination) s)
    (hboth : s.delivered = true ∧ s.refunded = true) :
    ∃ i, s.record = some i ∧ EndAcceptedBy H roots bk (sub i) ∧ EndBreak bk (sub i) := by
  have hauth := run_authorized (initial_authorized _ source destination) hrun
  obtain ⟨i, hi, hfin⟩ := hauth.1 hboth.1
  obtain ⟨j, hj, hrec⟩ := hauth.2 hboth.2
  have hij : i = j := Option.some.inj (hi.symm.trans hj)
  subst hij
  rcases hrec with ⟨l, hl, k, hb⟩ | ⟨hl, ha⟩
  · obtain ⟨n, hn, hmem⟩ := hfin l hl
    exact absurd hmem (beginVia_never_finalized hH hb n hn)
  · exact ⟨i, hi, ha, acceptedEnd_onTime_locates_break hH hagg (hfin _ hl) ha⟩

theorem pinned_bridge_no_double_payment_or_break {h : MerkleSpec.Hash} {ze : UInt256}
    {H : History} {roots : Roots} {bk : Backing h ze roots} (hH : H.Valid)
    (hagg : ∀ k, RootAggregates H (roots k)) {flow : Transfer → List Leg}
    {sub : Transfer → EndSubmission} {source destination : ℕ} {s : State}
    (hrun : Run (pinnedEvidence H roots bk flow sub) (initial source destination) s) :
    ¬ (s.delivered = true ∧ s.refunded = true)
      ∨ ∃ i, s.record = some i ∧ EndAcceptedBy H roots bk (sub i)
          ∧ EndBreak bk (sub i) := by
  by_cases hboth : s.delivered = true ∧ s.refunded = true
  · exact Or.inr (pinned_double_payment_locates_break hH hagg hrun hboth)
  · exact Or.inl hboth

theorem pinned_bridge_value_conserved_or_break {h : MerkleSpec.Hash} {ze : UInt256}
    {H : History} {roots : Roots} {bk : Backing h ze roots} (hH : H.Valid)
    (hagg : ∀ k, RootAggregates H (roots k)) {flow : Transfer → List Leg}
    {sub : Transfer → EndSubmission} {source destination : ℕ} {s : State}
    (hrun : Run (pinnedEvidence H roots bk flow sub) (initial source destination) s) :
    accounted s = source + destination
      ∨ ∃ i, s.record = some i ∧ EndAcceptedBy H roots bk (sub i)
          ∧ EndBreak bk (sub i) := by
  rcases value_conserved_unless_double_paid hrun with hboth | hacc
  · exact Or.inr (pinned_double_payment_locates_break hH hagg hrun hboth)
  · exact Or.inl hacc

/-! ## The concrete instances -/

theorem demoTime_le {n : ℕ} (hn : n ≤ 1) : demoTime n = 0 := by
  simp [demoTime, hn]

theorem demoTime_gt {n : ℕ} (hn : 1 < n) : demoTime n = 2 := by
  have hn' : ¬ n ≤ 1 := by omega
  simp [demoTime, hn']

theorem demoTime_monotone : Monotone demoTime := by
  intro a b hab
  by_cases ha : a ≤ 1
  · rw [demoTime_le ha]
    by_cases hb : b ≤ 1
    · rw [demoTime_le hb]
    · rw [demoTime_gt (by omega)]
      decide
  · rw [demoTime_gt (by omega), demoTime_gt (by omega)]

theorem haltedHistory_valid : haltedHistory.Valid where
  guarded := fun _ _ => Or.inl rfl
  genesis := fun _ => rfl
  monotone_time := fun _ => demoTime_monotone

theorem one_mem_committedLeaves : (1 : UInt256) ∈ keys committedLeaves :=
  imtInsert_key_mem (Finset.mem_singleton_self _)

theorem committedHistory_valid : committedHistory.Valid where
  guarded := by
    intro c n
    cases n with
    | zero =>
      refine Or.inr ⟨⟨0, 0⟩, 1, Finset.mem_singleton_self _, by decide, Or.inl rfl, ?_, rfl⟩
      show (1 : UInt256) ∉ keys {⟨0, 0⟩}
      simp [keys]
    | succ m => exact Or.inl rfl
  genesis := fun _ => rfl
  monotone_time := fun _ => demoTime_monotone

/-- Every history on the demo clock aggregates into `Contracts.Timeout.demoRoot`. -/
theorem demoTime_aggregates {H : History} (ht : ∀ c n, H.settledAt c n = demoTime n) :
    RootAggregates H Contracts.Timeout.demoRoot := by
  intro c n hn
  rw [ht] at hn
  show n ≤ 1
  by_contra hc
  rw [demoTime_gt (by omega)] at hn
  exact absurd hn (by decide)

theorem halted_aggregates : RootAggregates haltedHistory Contracts.Timeout.demoRoot :=
  demoTime_aggregates fun _ _ => rfl

theorem committed_aggregates : RootAggregates committedHistory Contracts.Timeout.demoRoot :=
  demoTime_aggregates fun _ _ => rfl

theorem halted_never_on_time {l : Leg} (hv : l.commitValue ≠ 0) (n : ℕ) :
    l.commitValue ∉ keys (haltedHistory.tree l.sourceChain n) := by
  show l.commitValue ∉ keys {⟨0, 0⟩}
  simpa [keys] using hv

theorem genesis_gap_one : GapWitness {⟨0, 0⟩} 1 :=
  ⟨⟨0, 0⟩, Finset.mem_singleton_self _, by decide, Or.inl rfl⟩

/-- On the demo clock, `demoRoot` holds only in-time batches: no BEGIN-branch timeout for a
deadline-`0` leg. -/
theorem no_begin_demoRoot {H : History} (ht : ∀ c n, H.settledAt c n = demoTime n) {l : Leg}
    (hD : l.deadline = 0) : ¬ BeginVia H Contracts.Timeout.demoRoot l := by
  rintro ⟨_, L, hL, hlate, _⟩
  rw [ht, demoTime_le hL, hD] at hlate
  exact absurd hlate (lt_irrefl 0)

/-- The halted chain's END-branch timeout against `demoRoot` (its last batch, `1`). -/
theorem halted_endVia : EndVia haltedHistory Contracts.Timeout.demoRoot demoLeg :=
  endVia_iff_endLastVia.mpr ⟨by decide, by decide, genesis_gap_one⟩

theorem committed_onTime : OnTime committedHistory demoLeg :=
  ⟨1, by decide, one_mem_committedLeaves⟩

theorem committed_onTimeIn : OnTimeIn committedHistory Contracts.Timeout.demoRoot demoLeg :=
  ⟨1, le_refl 1, by decide, one_mem_committedLeaves⟩

theorem demo_prepare :
    Prepare (initial 1 0) sampleTransfer (burn (initial 1 0) sampleTransfer) := by
  simp [Prepare, initial, sampleTransfer, burn]

theorem demo_execute : Execute (burn (initial 1 0) sampleTransfer) sampleTransfer sampleTransfer
    (mint (burn (initial 1 0) sampleTransfer) sampleTransfer) := by
  simp [Execute, Ready, burn, initial]

theorem demo_recover : Recover (burn (initial 1 0) sampleTransfer) sampleTransfer
    (restore (burn (initial 1 0) sampleTransfer) sampleTransfer) := by
  simp [Recover, burn, initial]

theorem demo_recover_after_mint :
    Recover (mint (burn (initial 1 0) sampleTransfer) sampleTransfer) sampleTransfer
      (restore (mint (burn (initial 1 0) sampleTransfer) sampleTransfer) sampleTransfer) := by
  simp [Recover, mint, burn, initial]

/-- Prepare, then recover. -/
theorem demo_refund_run {E : Evidence} (hr : E.recover sampleTransfer) :
    Run E (initial 1 0) (restore (burn (initial 1 0) sampleTransfer) sampleTransfer) :=
  .tail (.tail .refl (.prepare demo_prepare)) (.recover hr demo_recover)

/-- Prepare, execute, then recover: both outcomes. -/
theorem demo_double_run {E : Evidence} (hf : E.finalize sampleTransfer)
    (hr : E.recover sampleTransfer) :
    Run E (initial 1 0)
      (restore (mint (burn (initial 1 0) sampleTransfer) sampleTransfer) sampleTransfer) :=
  .tail (.tail (.tail .refl (.prepare demo_prepare)) (.execute hf demo_execute))
    (.recover hr demo_recover_after_mint)

/-- The single prerequisite of every demo transfer. -/
abbrev demoFlow : Transfer → List Leg := fun _ => [demoLeg]

theorem mem_demoFlow {j : Transfer} {l : Leg} (hl : l ∈ demoFlow j) : l = demoLeg :=
  List.mem_singleton.mp hl

/-- With the halted chain, no demo transfer can execute. -/
theorem halted_not_finalized (j : Transfer) : ¬ ∀ l ∈ demoFlow j, OnTime haltedHistory l := by
  intro hall
  obtain ⟨n, _, hmem⟩ := hall demoLeg (List.mem_singleton_self _)
  exact halted_never_on_time (l := demoLeg) (by decide) n hmem

/-- The demo flow on a single imported root, with the hash-level backing. -/
abbrev demoRoots : Roots := fun _ => Contracts.Timeout.demoRoot

/-! ### §1 witnesses -/

theorem end_branch_refund_witness : Properties.EndBranchRefundWitness := by
  have hend : MissingEnd haltedHistory demoLeg := by
    refine ⟨1, 1, by decide, by decide, ?_, genesis_gap_one⟩
    intro n hn
    show (1 : UInt256) ≤ demoTime n
    rw [demoTime_gt hn]
    decide
  exact ⟨haltedHistory, demoFlow, sampleTransfer, _, haltedHistory_valid,
    ⟨demoLeg, List.mem_singleton_self _, hend⟩,
    demo_refund_run ⟨demoLeg, List.mem_singleton_self _, Or.inr hend⟩, rfl, rfl⟩

theorem onTime_leg_executes_witness : Properties.OnTimeLegExecutesWitness := by
  have hall : ∀ l ∈ demoFlow sampleTransfer, OnTime committedHistory l := by
    intro l hl
    rw [mem_demoFlow hl]
    exact committed_onTime
  exact ⟨committedHistory, demoFlow, sampleTransfer, _, committedHistory_valid, hall,
    .tail (.tail .refl (.prepare demo_prepare)) (.execute hall demo_execute), rfl, rfl⟩

/-! ### §2 witnesses and countermodels -/

theorem lateTime_monotone : Monotone lateTime := by
  intro a b hab
  unfold lateTime
  by_cases ha0 : a = 0
  · subst ha0
    by_cases hb0 : b = 0
    · simp [hb0]
    · by_cases hb1 : b = 1
      · simp [hb1]
      · simp [hb0, hb1]
  · by_cases ha1 : a = 1
    · subst ha1
      by_cases hb1 : b = 1
      · simp [hb1]
      · have hb0 : b ≠ 0 := by omega
        simp [hb0, hb1]
    · have hb0 : b ≠ 0 := by omega
      have hb1 : b ≠ 1 := by omega
      simp [ha0, ha1, hb0, hb1]

theorem lateHistory_valid : lateHistory.Valid where
  guarded := fun _ _ => Or.inl rfl
  genesis := fun _ => rfl
  monotone_time := fun _ => lateTime_monotone

theorem late_aggregates : RootAggregates lateHistory Contracts.Timeout.demoRoot := by
  intro c n hn
  show n ≤ 1
  by_contra hc
  have h2 : lateHistory.settledAt c n = 2 := by
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    show lateTime n = 2
    simp [lateTime, hn0, hn1]
  rw [h2] at hn
  exact absurd hn (by decide)

/-- Batch `1` settled at time `1`, after the deadline, inside `demoRoot`; its BEGIN tree is
the genesis snapshot. -/
theorem late_beginVia : BeginVia lateHistory Contracts.Timeout.demoRoot demoLeg :=
  ⟨by decide, 1, le_refl 1, by decide, genesis_gap_one⟩

theorem begin_branch_refund_witness : Properties.BeginBranchRefundWitness :=
  ⟨lateHistory, demoRoots, demoFlow, sampleTransfer, _, lateHistory_valid,
    fun _ => late_aggregates, ⟨demoLeg, List.mem_singleton_self _, 0, late_beginVia⟩,
    demo_refund_run ⟨demoLeg, List.mem_singleton_self _, 0, Or.inl late_beginVia⟩, rfl, rfl⟩

theorem begin_only_incomplete : Properties.BeginOnlyIncomplete :=
  ⟨haltedHistory, Contracts.Timeout.demoRoot, demoLeg, haltedHistory_valid, halted_aggregates,
    by decide, fun n _ => halted_never_on_time (by decide) n, by decide,
    no_begin_demoRoot (fun _ _ => rfl) rfl⟩

theorem halted_chain_needs_end_branch : Properties.HaltedChainNeedsEndBranch := by
  have hagg : ∀ k, RootAggregates haltedHistory (demoRoots k) := fun _ => halted_aggregates
  have hnobegin : ∀ (j : Transfer), ∀ l ∈ demoFlow j, ∀ k,
      ¬ BeginVia haltedHistory (demoRoots k) l := by
    intro j l hl k
    rw [mem_demoFlow hl]
    exact no_begin_demoRoot (fun _ _ => rfl) rfl
  have hnorecover : ∀ j, ¬ (beginOnlyEvidence haltedHistory demoRoots demoFlow).recover j := by
    rintro j ⟨l, hl, k, hb⟩
    exact hnobegin j l hl k hb
  -- with the BEGIN branch only, neither flag can ever be raised
  have hflags : ∀ {s t : State},
      Authorized (beginOnlyEvidence haltedHistory demoRoots demoFlow) s →
        Run (beginOnlyEvidence haltedHistory demoRoots demoFlow) s t →
          t.delivered = false ∧ t.refunded = false := by
    intro s t hs hrun
    have ht := run_authorized hs hrun
    constructor
    · cases hd : t.delivered with
      | false => rfl
      | true =>
        obtain ⟨j, _, hfin⟩ := ht.1 hd
        exact absurd hfin (halted_not_finalized j)
    · cases hr : t.refunded with
      | false => rfl
      | true =>
        obtain ⟨j, _, hrec⟩ := ht.2 hr
        exact absurd hrec (hnorecover j)
  refine ⟨haltedHistory, demoRoots, demoFlow, sampleTransfer, haltedHistory_valid, hagg, ?_,
    hnobegin, ?_, ?_, ⟨demoLeg, List.mem_singleton_self _, 0, halted_endVia⟩, ?_⟩
  · intro j l hl
    rw [mem_demoFlow hl]
    exact ⟨by decide, fun n _ => halted_never_on_time (by decide) n⟩
  · intro s hrun
    exact hflags (initial_authorized _ _ _) hrun
  · intro s hrun
    have hauth0 : Authorized (beginOnlyEvidence haltedHistory demoRoots demoFlow)
        (burn (initial sampleTransfer.amount 0) sampleTransfer) := by
      simp [Authorized, burn, initial]
    obtain ⟨hd, hr⟩ := hflags hauth0 hrun
    have hrec : s.record = some sampleTransfer := run_preserves_committed_input rfl hrun
    simp [limbo, hd, hr, hrec]
  · exact ⟨_, demo_refund_run ⟨demoLeg, List.mem_singleton_self _, 0, Or.inr halted_endVia⟩,
      rfl, rfl, rfl⟩

theorem halted_adapter_missing_cites_unimported_batch :
    Properties.HaltedAdapterMissingCitesUnimportedBatch := by
  refine ⟨haltedHistory, demoRoots, demoLeg, haltedHistory_valid, fun _ => halted_aggregates,
    ?_, ?_, fun _ => no_begin_demoRoot (fun _ _ => rfl) rfl, ⟨0, halted_endVia⟩⟩
  · -- batch 2 settles at time 2, after the deadline; it is in no imported root
    obtain ⟨W, hW, hlow, hwin⟩ := genesis_gap_one
    refine ⟨1, W, ?_, hW, hlow, hwin⟩
    show (0 : UInt256) < demoTime 2
    rw [demoTime_gt (by norm_num)]
    decide
  · intro n hlate k
    show 1 < n + 1
    by_contra hle
    have h0 : haltedHistory.settledAt demoLeg.sourceChain (n + 1) = 0 := demoTime_le (by omega)
    rw [h0] at hlate
    exact absurd hlate (lt_irrefl 0)

theorem checked_execution_remains_possible {H : History} {roots : Roots} (hH : H.Valid)
    (hagg : ∀ k, RootAggregates H (roots k)) (flow : Transfer → List Leg) {s p t : State}
    {i : Transfer} (hp : Prepare s i p) (hc : (checkedEvidence H roots flow).finalize i)
    (hrun : Run (checkedEvidence H roots flow) p t) :
    t.refunded = false ∧
      (t.delivered = true ∨ ∃ u, AuthorizedExecution (checkedEvidence H roots flow) t i i u) :=
  prepared_execution_remains_possible (checkedEvidence_sound hH hagg flow) hp hc hrun

theorem checked_execution_witness : Properties.CheckedExecutionWitness := by
  have hall : (checkedEvidence committedHistory demoRoots demoFlow).finalize sampleTransfer := by
    intro l hl
    rw [mem_demoFlow hl]
    exact committed_onTime
  exact ⟨committedHistory, demoRoots, demoFlow, _, _, sampleTransfer, committedHistory_valid,
    fun _ => committed_aggregates, demo_prepare, hall, _, hall, demo_execute⟩

theorem stale_root_double_pays : Properties.StaleRootDoublePays := by
  have hfin : ∀ l ∈ demoFlow sampleTransfer, OnTime committedHistory l := by
    intro l hl
    rw [mem_demoFlow hl]
    exact committed_onTime
  have hend : EndVia committedHistory (staleRoots 0) demoLeg :=
    endVia_iff_endLastVia.mpr ⟨by decide, by decide, genesis_gap_one⟩
  refine ⟨committedHistory, staleRoots, demoFlow, _, committedHistory_valid, ?_, ?_,
    demo_double_run hfin ⟨demoLeg, List.mem_singleton_self _, 0, Or.inr hend⟩,
    rfl, rfl, by decide⟩
  · -- root 0 was created at time 1, after batch 1 settled at time 0, yet stops at batch 0
    intro hall
    exact absurd (hall 0 0 1 (by decide)) (by decide)
  · intro j l hl
    rw [mem_demoFlow hl]
    exact ⟨1, committed_onTimeIn⟩

theorem unchecked_end_double_pays : Properties.UncheckedEndDoublePays := by
  have hfin : ∀ l ∈ demoFlow sampleTransfer, OnTime committedHistory l := by
    intro l hl
    rw [mem_demoFlow hl]
    exact committed_onTime
  -- batch 0 is in time, inside the root, and lacks the leg, but it is not the root's last batch
  have hend : EndUncheckedVia committedHistory Contracts.Timeout.demoRoot demoLeg :=
    ⟨by decide, 0, by decide, by decide, genesis_gap_one⟩
  refine ⟨committedHistory, demoRoots, demoFlow, _, committedHistory_valid,
    fun _ => committed_aggregates, ?_,
    demo_double_run hfin ⟨demoLeg, List.mem_singleton_self _, 0, Or.inr hend⟩,
    rfl, rfl, by decide⟩
  intro j l hl
  rw [mem_demoFlow hl]
  exact ⟨0, committed_onTimeIn⟩

/-! ### §3 witnesses -/

/-- The honest END submission for the halted chain: batch `1`, the last of `demoBacking`. -/
def honestSubmission : EndSubmission :=
  ⟨demoLeg, 0, 1, MerkleSpec.Verifier.honestSibs MerkleSpec.LastLeaf.demoHash 0 [5, 7] 1, 7⟩

theorem pinned_bridge_refund_witness : Properties.PinnedBridgeRefundWitness := by
  have ha : EndAcceptedBy haltedHistory demoRoots (fun _ => Contracts.Timeout.demoBacking)
      honestSubmission :=
    ⟨by decide, by decide, Contracts.Timeout.demo_endBranchAccepted.lastBatch, genesis_gap_one⟩
  have hnb : ¬ EndBreak (roots := demoRoots) (fun _ => Contracts.Timeout.demoBacking)
      honestSubmission := by
    rintro (hpb | hpc)
    · rcases hpb with ⟨_, _, hlt, _⟩ | ⟨hlt, _⟩ <;> exact absurd hlt (by decide)
    · exact MerkleSpec.Verifier.honest_walk_no_collision MerkleSpec.LastLeaf.demoHash 0
        [5, 7] 2 1 hpc
  exact ⟨MerkleSpec.LastLeaf.demoHash, 0, haltedHistory, demoRoots,
    fun _ => Contracts.Timeout.demoBacking, demoFlow, fun _ => honestSubmission, sampleTransfer, _,
    haltedHistory_valid, fun _ => halted_aggregates,
    demo_refund_run (Or.inr ⟨List.mem_singleton_self _, ha⟩), rfl, rfl, ha, hnb,
    MerkleSpec.LastLeaf.demo_collides⟩

/-- The forged END submission: batch `0` of `forgedBacking`, on its honest path. -/
def forgedSubmission : EndSubmission :=
  ⟨demoLeg, 0, 0, MerkleSpec.Verifier.honestSibs MerkleSpec.LastLeaf.demoHash 0 [5, 0] 0, 5⟩

theorem forged_lastBatch_accepted :
    Contracts.Timeout.LastBatchAccepted forgedBacking 0 0 forgedSubmission.sibs 5 := by
  refine ⟨by decide, ?_, ?_⟩
  · exact MerkleSpec.Verifier.honest_walk_root MerkleSpec.LastLeaf.demoHash 0 [5, 0] 1 0
      (by norm_num)
  · intro l hl _
    obtain rfl : l = 0 := by
      change l < 1 at hl
      omega
    decide

theorem forged_lastBatch_locates_break : Properties.ForgedLastBatchLocatesBreak := by
  have hfin : ∀ l ∈ demoFlow sampleTransfer, OnTime committedHistory l := by
    intro l hl
    rw [mem_demoFlow hl]
    exact committed_onTime
  have ha : EndAcceptedBy committedHistory demoRoots (fun _ => forgedBacking) forgedSubmission :=
    ⟨by decide, by decide, forged_lastBatch_accepted, genesis_gap_one⟩
  exact ⟨MerkleSpec.LastLeaf.demoHash, 0, committedHistory, demoRoots, fun _ => forgedBacking,
    demoFlow, fun _ => forgedSubmission, sampleTransfer, _, committedHistory_valid,
    fun _ => committed_aggregates, committed_onTime,
    demo_double_run hfin (Or.inr ⟨List.mem_singleton_self _, ha⟩), rfl, rfl, by decide, rfl, ha,
    .entryIsEmpty (by decide) (by decide)⟩

end Applications.BurnMintBridge.EndBranch

/-! ## Certificates -/

namespace Applications.BurnMintBridge.EndBranch

open Properties.PreparedBridge

theorem MissingEndImpliesMissing : Properties.MissingEndImpliesMissing :=
  fun _ _ h => missingEnd_implies_missing h
theorem MissingEndIffAbsence : Properties.MissingEndIffAbsence :=
  fun _ hH _ => missingEnd_iff_absence hH
theorem MissingEitherNeverFinalized : Properties.MissingEitherNeverFinalized :=
  fun _ hH _ hm n hn => missingEither_never_finalized hH hm n hn
theorem OnTimeExcludesMissingEither : Properties.OnTimeExcludesMissingEither :=
  fun _ hH _ hon => onTime_excludes_missingEither hH hon
theorem EvidenceEitherSound : Properties.EvidenceEitherSound :=
  fun _ hH flow => evidenceEither_sound hH flow
theorem PreparedBridgeNoDoublePaymentEither : Properties.PreparedBridgeNoDoublePaymentEither :=
  fun _ hH flow _ _ _ hrun => reachable_resolution_exclusive (evidenceEither_sound hH flow) hrun
theorem PreparedBridgeValueConservedEither : Properties.PreparedBridgeValueConservedEither :=
  fun _ hH flow _ _ _ hrun => reachable_value_conserved (evidenceEither_sound hH flow) hrun
theorem RunMonotone : Properties.RunMonotone :=
  fun _ _ hf hr _ _ h => run_monotone hf hr h
theorem EvidenceEitherRunsAreAdapterRuns : Properties.EvidenceEitherRunsAreAdapterRuns :=
  fun _ _ _ _ => evidenceEither_runs_iff
theorem EndBranchRefundWitness : Properties.EndBranchRefundWitness :=
  end_branch_refund_witness
theorem OnTimeLegExecutesWitness : Properties.OnTimeLegExecutesWitness :=
  onTime_leg_executes_witness

theorem EndCheckIffLastInRoot : Properties.EndCheckIffLastInRoot :=
  fun _ _ _ => endVia_iff_endLastVia
theorem BeginViaNeverFinalized : Properties.BeginViaNeverFinalized :=
  fun _ _ hH _ hb n hn => beginVia_never_finalized hH hb n hn
theorem EndViaNeverFinalized : Properties.EndViaNeverFinalized :=
  fun _ _ hH hagg _ he n hn => endVia_never_finalized hH hagg he n hn
theorem TimeoutViaImpliesMissing : Properties.TimeoutViaImpliesMissing :=
  fun _ _ hH hagg _ ht => timeoutVia_implies_missing hH hagg ht
theorem CheckedEvidenceSound : Properties.CheckedEvidenceSound :=
  fun _ _ hH hagg flow => checkedEvidence_sound hH hagg flow
theorem CheckedBridgeNoDoublePayment : Properties.CheckedBridgeNoDoublePayment :=
  fun _ _ hH hagg flow _ _ _ hrun => checked_bridge_no_double_payment hH hagg flow hrun
theorem CheckedBridgeValueConserved : Properties.CheckedBridgeValueConserved :=
  fun _ _ hH hagg flow _ _ _ hrun => checked_bridge_value_conserved hH hagg flow hrun
theorem TimeoutComplete : Properties.TimeoutComplete :=
  fun _ hH _ hv hnever R hroot => timeout_complete hH hv hnever R hroot
theorem BeginBranchRefundWitness : Properties.BeginBranchRefundWitness :=
  begin_branch_refund_witness
theorem BeginOnlyIncomplete : Properties.BeginOnlyIncomplete :=
  begin_only_incomplete
theorem HaltedChainNeedsEndBranch : Properties.HaltedChainNeedsEndBranch :=
  halted_chain_needs_end_branch
theorem HaltedAdapterMissingCitesUnimportedBatch :
    Properties.HaltedAdapterMissingCitesUnimportedBatch :=
  halted_adapter_missing_cites_unimported_batch
theorem CheckedExecutionRemainsPossible : Properties.CheckedExecutionRemainsPossible :=
  fun _ _ hH hagg flow _ _ _ _ hp hc hrun =>
    checked_execution_remains_possible hH hagg flow hp hc hrun
theorem CheckedExecutionWitness : Properties.CheckedExecutionWitness :=
  checked_execution_witness
theorem TimedOutTransferRefundEnabled : Properties.TimedOutTransferRefundEnabled :=
  fun _ _ _ hH _ _ hl hv hnever _ hroot _ hrec hr =>
    timedOut_transfer_refund_enabled hH hl hv hnever hroot hrec hr
theorem StaleRootDoublePays : Properties.StaleRootDoublePays :=
  stale_root_double_pays
theorem UncheckedEndDoublePays : Properties.UncheckedEndDoublePays :=
  unchecked_end_double_pays

theorem AcceptedEndOnTimeLocatesBreak : Properties.AcceptedEndOnTimeLocatesBreak :=
  fun _ _ _ _ _ hH hagg _ hon ha => acceptedEnd_onTime_locates_break hH hagg hon ha
theorem PinnedBridgeNoDoublePaymentOrBreak : Properties.PinnedBridgeNoDoublePaymentOrBreak :=
  fun _ _ _ _ _ hH hagg _ _ _ _ _ hrun => pinned_bridge_no_double_payment_or_break hH hagg hrun
theorem PinnedBridgeValueConservedOrBreak : Properties.PinnedBridgeValueConservedOrBreak :=
  fun _ _ _ _ _ hH hagg _ _ _ _ _ hrun => pinned_bridge_value_conserved_or_break hH hagg hrun
theorem PinnedBridgeRefundWitness : Properties.PinnedBridgeRefundWitness :=
  pinned_bridge_refund_witness
theorem ForgedLastBatchLocatesBreak : Properties.ForgedLastBatchLocatesBreak :=
  forged_lastBatch_locates_break

theorem ValueConservedUnlessDoublePaid : Properties.ValueConservedUnlessDoublePaid :=
  fun _ _ _ _ h => value_conserved_unless_double_paid h

end Applications.BurnMintBridge.EndBranch
