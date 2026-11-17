import EraSpec.Contracts.L2InteropCommitmentTree.Properties.HintSearchAtHead
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.InitOnce

/-!
# Proofs: the head's unbounded walk, against the pin's five-hop search

Proofs of `EraSpec.Contracts.L2InteropCommitmentTree.Properties.HintSearchAtHead`.

Two facts do the work.  Once the walk exits, more hops do not change its result
(`lowSearch_mono_atHead`), so the walk is deterministic and equals the search with
`leafCount` hops on a valid tree.  And from its own landing index the walk makes no hop
(`lowSearch_exit`), so a head insert is the pin's insert with the landing index as hint
(`insertChecks_of_guard`).  The run results then follow by relabelling every insert of a
head run from the predeploy, whose initialized states are valid (`txRunAtHead_states`).
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract

/-! ## The walk -/

/-- **MORE HOPS DO NOT CHANGE AN EXITED WALK.** -/
theorem lowSearch_mono_atHead {T : Tree} {v : UInt256} :
    ∀ (n i j : ℕ), lowSearch T v n i = some j → ∀ m, n ≤ m → lowSearch T v m i = some j := by
  intro n
  induction n with
  | zero =>
    intro i j h m _
    unfold lowSearch at h
    by_cases hc : (T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v
    · rw [ite_eq_left hc] at h
      exact absurd h (by simp)
    · rw [ite_eq_right hc] at h
      cases Option.some.inj h
      exact lowSearch_exit hc m
  | succ n ih =>
    intro i j h m hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    unfold lowSearch at h ⊢
    by_cases hc : (T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v
    · rw [ite_eq_left hc] at h ⊢
      exact ih _ _ h m' (by omega)
    · rw [ite_eq_right hc] at h ⊢
      exact h

theorem walkAtHead_det {T : Tree} {v : UInt256} {hint low low' : ℕ}
    (h : WalkSucceedsAtHead T v hint low) (h' : WalkSucceedsAtHead T v hint low') :
    low = low' := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨n', hn'⟩ := h'
  have h1 := lowSearch_mono_atHead n hint low hn (max n n') (le_max_left _ _)
  have h2 := lowSearch_mono_atHead n' hint low' hn' (max n n') (le_max_right _ _)
  rw [h1] at h2
  exact Option.some.inj h2

theorem walkAtHead_iff_leafCount {T : Tree} (hV : Valid T) (v : UInt256) (hint low : ℕ)
    (hi : hint < T.leafCount) :
    WalkSucceedsAtHead T v hint low ↔ lowSearch T v T.leafCount hint = some low := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := lowSearch_terminates hV v hint hi
    rw [walkAtHead_det h ⟨_, hj⟩]
    exact hj
  · intro h
    exact ⟨_, h⟩

theorem walkAtHead_terminates {T : Tree} (hV : Valid T) (v : UInt256) (hint : ℕ)
    (hi : hint < T.leafCount) : ∃ low, WalkSucceedsAtHead T v hint low := by
  obtain ⟨j, hj⟩ := lowSearch_terminates hV v hint hi
  exact ⟨j, _, hj⟩

/-! ## The insert -/

theorem insertChecksAtHead_guard {T : Tree} (hV : Valid T) {v : UInt256} {hint low : ℕ}
    (h : InsertChecksAtHead T v hint low) : InsertGuard T v low := by
  obtain ⟨n, hn⟩ := h.walk
  exact search_yields_guard hV h.initialized h.nonzero h.unregistered h.hintInBounds
    h.hintBelow hn

/-- On a valid tree, at most one index carries the guard for a value: the leaf whose window
straddles it.  The windows are strict because the value is not a key (`fresh`), and two
strict windows around one value would contradict `GapSound`. -/
theorem insertGuard_unique {T : Tree} (hV : Valid T) {v : UInt256} {j j' : ℕ}
    (hg : InsertGuard T v j) (hg' : InsertGuard T v j') : j = j' := by
  have hnot : v ∉ keys (toAbs T) := dedup_gate_sound hV hg.nonzero hg.fresh
  have hmem : lowAbs T j ∈ toAbs T := lowAbs_mem hg.inBounds
  have hmem' : lowAbs T j' ∈ toAbs T := lowAbs_mem hg'.inBounds
  have hwin : (T.leaf j).nextValue = 0 ∨ v < (T.leaf j).nextValue :=
    window_strict_of_not_mem hV.absSound.2.2.1 hmem hnot hg.window
  have hwin' : (T.leaf j').nextValue = 0 ∨ v < (T.leaf j').nextValue :=
    window_strict_of_not_mem hV.absSound.2.2.1 hmem' hnot hg'.window
  rcases lt_trichotomy (T.leaf j).value (T.leaf j').value with hlt | heq | hgt
  · exfalso
    obtain ⟨hnz, hle⟩ := hV.absSound.1 _ hmem _ hmem' hlt
    rcases hwin with h0 | hv
    · exact hnz h0
    · exact absurd (lt_of_lt_of_le hv hle) (not_lt.mpr hg'.lowBelow.le)
  · exact hV.idxInj j hg.inBounds j' hg'.inBounds heq
  · exfalso
    obtain ⟨hnz, hle⟩ := hV.absSound.1 _ hmem' _ hmem hgt
    rcases hwin' with h0 | hv
    · exact hnz h0
    · exact absurd (lt_of_lt_of_le hv hle) (not_lt.mpr hg.lowBelow.le)

theorem insertAtHead_landing_hint_independent {T : Tree} (hV : Valid T) {v : UInt256}
    {hint hint' low low' : ℕ} (h : InsertChecksAtHead T v hint low)
    (h' : InsertChecksAtHead T v hint' low') : low = low' :=
  insertGuard_unique hV (insertChecksAtHead_guard hV h) (insertChecksAtHead_guard hV h')

theorem insertAtHead_enabled_iff {T : Tree} (hV : Valid T) (v : UInt256) (hint : ℕ) :
    (∃ low, InsertChecksAtHead T v hint low)
      ↔ Initialized T ∧ v ≠ 0 ∧ T.valueToIndex v = 0 ∧ hint < T.leafCount
        ∧ (T.leaf hint).value < v := by
  constructor
  · rintro ⟨low, h⟩
    exact ⟨h.initialized, h.nonzero, h.unregistered, h.hintInBounds, h.hintBelow⟩
  · rintro ⟨hinit, hv, hreg, hi, hlow⟩
    obtain ⟨low, hw⟩ := walkAtHead_terminates hV v hint hi
    exact ⟨low, hinit, hv, hreg, hi, hlow, hw⟩

/-- Every pin insert is a head insert (no validity needed). -/
lemma insertChecksAtHead_of_pin {T : Tree} {v : UInt256} {hint low : ℕ}
    (h : InsertChecks T v hint low) : InsertChecksAtHead T v hint low :=
  ⟨h.initialized, h.nonzero, h.unregistered, h.hintInBounds, h.hintBelow, _, h.search⟩

/-- On a valid tree, a head insert passes the pin's checks from its landing index. -/
lemma pin_insertChecks_of_atHead {T : Tree} (hV : Valid T) {v : UInt256} {hint low : ℕ}
    (h : InsertChecksAtHead T v hint low) : InsertChecks T v low low :=
  insertChecks_of_guard (insertChecksAtHead_guard hV h)

theorem honest_insert_succeeds_at_head :
    Reaches setup (chainTree 6)
      ∧ (∀ low, ¬ InsertChecks (chainTree 6) 7 0 low)
      ∧ InsertChecksAtHead (chainTree 6) 7 0 6 := by
  obtain ⟨hR, hcount, hval, hpin, hfull, hguard⟩ := HonestInsertRevertsAtDeployedFuel
  refine ⟨hR, fun low hch => ?_, ?_⟩
  · have := hch.search
    rw [hpin] at this
    exact absurd this (by simp)
  · exact ⟨hguard.initialized, hguard.nonzero, hguard.fresh, by rw [hcount]; omega, hval,
      _, hfull⟩

/-! ## Transactions -/

lemma txStepAtHead_leafCount {K : Roles} {T U : Tree} {c : Caller} {call : Call}
    (h : TxStepAtHead K T c call U) : U.leafCount = T.leafCount + 1 := by
  cases h <;> rfl

lemma txStepAtHead_value_old {K : Roles} {T U : Tree} {c : Caller} {call : Call}
    (h : TxStepAtHead K T c call U) :
    ∀ i < T.leafCount, (U.leaf i).value = (T.leaf i).value := by
  cases h with
  | initL2 _ hg => intro i hi; omega
  | insert _ _ => intro i hi; exact insert_value_old hi

lemma txStepAtHead_initL2_inv {K : Roles} {T U : Tree} {c : Caller}
    (h : TxStepAtHead K T c .initL2 U) : c = K.upgrader ∧ T.leafCount = 0 ∧ U = setupWrites T := by
  cases h with
  | initL2 hc hg => exact ⟨hc, hg, rfl⟩

theorem pin_txStep_is_txStepAtHead {K : Roles} {T U : Tree} {c : Caller} {call : Call}
    (h : TxStep K T c call U) : TxStepAtHead K T c call U := by
  cases h with
  | initL2 hc hg => exact TxStepAtHead.initL2 hc hg
  | insert hc hch => exact TxStepAtHead.insert hc (insertChecksAtHead_of_pin hch)

/-- On a valid tree a head transaction is a guarded insert at its landing index. -/
lemma txStepAtHead_of_valid {K : Roles} {T U : Tree} {c : Caller} {call : Call} (hV : Valid T)
    (h : TxStepAtHead K T c call U) : ∃ v low, InsertGuard T v low ∧ U = insert T v low := by
  cases h with
  | initL2 _ hg => exact absurd hg (Nat.pos_iff_ne_zero.mp hV.occupied)
  | insert _ hch => exact ⟨_, _, insertChecksAtHead_guard hV hch, rfl⟩

theorem txStepAtHead_relabel {K : Roles} {T U : Tree} {c : Caller} {call : Call} (hV : Valid T)
    (h : TxStepAtHead K T c call U) : TxStep K T c (relabelCallAtHead T call) U := by
  cases h with
  | initL2 _ hg => exact absurd hg (Nat.pos_iff_ne_zero.mp hV.occupied)
  | @insert v hint low hc hch =>
    have hland : landingAtHead T v hint = low := by
      unfold landingAtHead
      rw [(walkAtHead_iff_leafCount hV v hint low hch.hintInBounds).mp hch.walk]
      rfl
    show TxStep K T c (.insert v (landingAtHead T v hint)) (insert T v low)
    rw [hland]
    exact TxStep.insert hc (pin_insertChecks_of_atHead hV hch)

/-- From the predeploy or a valid tree, a head transaction leaves a valid tree. -/
lemma txStepAtHead_valid {K : Roles} {T U : Tree} {c : Caller} {call : Call}
    (hT : T = predeploy ∨ Valid T) (h : TxStepAtHead K T c call U) : Valid U := by
  cases h with
  | initL2 _ hg =>
    rcases hT with hp | hv
    · subst hp
      rw [setupWrites_predeploy]
      exact setup_valid
    · exact absurd hg (Nat.pos_iff_ne_zero.mp hv.occupied)
  | insert _ hch =>
    rcases hT with hp | hv
    · subst hp
      exact absurd hch.initialized predeploy_not_initialized
    · exact insert_preserves_valid hv (insertChecksAtHead_guard hv hch)

/-- From the predeploy or a valid tree, a head transaction is a pin transaction, relabelled. -/
lemma txStepAtHead_relabel_of_state {K : Roles} {T U : Tree} {c : Caller} {call : Call}
    (hT : T = predeploy ∨ Valid T) (h : TxStepAtHead K T c call U) :
    TxStep K T c (relabelCallAtHead T call) U := by
  rcases hT with hp | hv
  · cases h with
    | initL2 hc hg => exact TxStep.initL2 hc hg
    | insert _ hch =>
      subst hp
      exact absurd hch.initialized predeploy_not_initialized
  · exact txStepAtHead_relabel hv h

/-! ## Runs -/

/-- Every state of a head run from the predeploy is the predeploy or valid. -/
theorem txRunAtHead_states {K : Roles} {R : ℕ → Tree} {tx : Trace} (hR : TxRunAtHead K R tx)
    (h0 : R 0 = predeploy) : ∀ n, R n = predeploy ∨ Valid (R n) := by
  intro n
  induction n with
  | zero => exact Or.inl h0
  | succ n ih =>
    rcases hR n with ⟨_, he⟩ | ⟨c, call, _, hs⟩
    · rw [he]
      exact ih
    · exact Or.inr (txStepAtHead_valid ih hs)

theorem relabelAtHead_keeps_shape (R : ℕ → Tree) (tx : Trace) (n : ℕ) :
    (relabelAtHead R tx n = none ↔ tx n = none)
      ∧ (∀ c : Caller, relabelAtHead R tx n = some (c, .initL2) ↔ tx n = some (c, .initL2))
      ∧ ∀ (c : Caller) (v : UInt256) (hint : ℕ), tx n = some (c, .insert v hint) →
          relabelAtHead R tx n = some (c, .insert v (landingAtHead (R n) v hint)) := by
  unfold relabelAtHead
  refine ⟨Option.map_eq_none_iff, fun c => ?_, fun c v hint h => ?_⟩
  · rcases htx : tx n with _ | ⟨c', call⟩
    · simp
    · cases call with
      | initL2 => simp [relabelCallAtHead]
      | insert v hint => simp [relabelCallAtHead]
  · rw [h]
    rfl

theorem txRunAtHead_relabel {K : Roles} {R : ℕ → Tree} {tx : Trace} (hR : TxRunAtHead K R tx)
    (h0 : R 0 = predeploy) : TxRun K R (relabelAtHead R tx) := by
  have hst := txRunAtHead_states hR h0
  intro n
  rcases hR n with ⟨hn, he⟩ | ⟨c, call, hn, hs⟩
  · left
    exact ⟨by simp [relabelAtHead, hn], he⟩
  · right
    refine ⟨c, relabelCallAtHead (R n) call, by simp [relabelAtHead, hn], ?_⟩
    exact txStepAtHead_relabel_of_state (hst n) hs

lemma txRunAtHead_step_appendOnly {K : Roles} {R : ℕ → Tree} {tx : Trace}
    (hR : TxRunAtHead K R tx) (n : ℕ) :
    (R n).leafCount ≤ (R (n + 1)).leafCount
      ∧ ∀ i < (R n).leafCount, ((R (n + 1)).leaf i).value = ((R n).leaf i).value := by
  rcases hR n with ⟨_, he⟩ | ⟨c, call, _, hs⟩
  · rw [he]
    exact ⟨le_rfl, fun _ _ => rfl⟩
  · exact ⟨by rw [txStepAtHead_leafCount hs]; omega, txStepAtHead_value_old hs⟩

theorem txRunAtHead_appendOnly (K : Roles) (R : ℕ → Tree) (tx : Trace)
    (hR : TxRunAtHead K R tx) (m n : ℕ) (hmn : m ≤ n) :
    (R m).leafCount ≤ (R n).leafCount
      ∧ ∀ i < (R m).leafCount, ((R n).leaf i).value = ((R m).leaf i).value :=
  appendOnly_of_steps (txRunAtHead_step_appendOnly hR) hmn

theorem txRunAtHead_keysMono (K : Roles) (R : ℕ → Tree) (tx : Trace)
    (hR : TxRunAtHead K R tx) (m n : ℕ) (hmn : m ≤ n) :
    keys (toAbs (R m)) ⊆ keys (toAbs (R n)) :=
  keys_subset_of_appendOnly (txRunAtHead_appendOnly K R tx hR m n hmn).1
    (txRunAtHead_appendOnly K R tx hR m n hmn).2

theorem initL2_at_most_once_at_head (K : Roles) (R : ℕ → Tree) (tx : Trace)
    (hR : TxRunAtHead K R tx) (m n : ℕ) (cm cn : Caller) (hm : tx m = some (cm, .initL2))
    (hn : tx n = some (cn, .initL2)) : m = n := by
  have sm := runOf_some hR hm
  have sn := runOf_some hR hn
  have hm0 := (txStepAtHead_initL2_inv sm).2.1
  have hn0 := (txStepAtHead_initL2_inv sn).2.1
  have hm1 := txStepAtHead_leafCount sm
  have hn1 := txStepAtHead_leafCount sn
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := (txRunAtHead_appendOnly K R tx hR (m + 1) n hlt).1
    omega
  · have := (txRunAtHead_appendOnly K R tx hR (n + 1) m hlt).1
    omega

theorem txRunAtHead_from_valid_is_run (K : Roles) (R : ℕ → Tree) (tx : Trace)
    (hR : TxRunAtHead K R tx) (h0 : Valid (R 0)) : Run R := by
  have hval : ∀ n, Valid (R n) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      rcases hR n with ⟨_, he⟩ | ⟨c, call, _, hs⟩
      · rw [he]
        exact ih
      · exact txStepAtHead_valid (Or.inr ih) hs
  intro n
  rcases hR n with ⟨_, he⟩ | ⟨c, call, _, hs⟩
  · exact Or.inl he
  · exact Or.inr (txStepAtHead_of_valid (hval n) hs)

/-! ## The witness -/

/-- The six honest inserts of the witness, each from its own low leaf. -/
private lemma stale_honest_checks (n : ℕ) (hn : n < 6) :
    InsertChecksAtHead (chainTree n) ((n + 1 : ℕ) : UInt256) n n := by
  interval_cases n <;>
    exact ⟨by unfold Initialized; decide, by decide, by decide, by decide, by decide, 0,
      by decide⟩

private lemma staleHintRun_succ_of_le {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 6) :
    staleHintRunAtHead n = chainTree (n - 1) ∧ staleHintRunAtHead (n + 1) = chainTree n := by
  unfold staleHintRunAtHead
  refine ⟨?_, ?_⟩
  · rw [ite_eq_right (by omega), Nat.min_eq_left (by omega)]
  · rw [ite_eq_right (by omega), Nat.min_eq_left (by omega), Nat.add_sub_cancel]

theorem staleHintRun_txRunAtHead (K : Roles) :
    TxRunAtHead K staleHintRunAtHead (staleHintTxAtHead K) := by
  intro n
  rcases Nat.lt_or_ge n 8 with hlt | hge
  · right
    by_cases h0 : n = 0
    · subst h0
      refine ⟨K.upgrader, .initL2, rfl, ?_⟩
      show TxStepAtHead K predeploy K.upgrader .initL2 (chainTree 0)
      rw [show chainTree 0 = setup from rfl, ← setupWrites_predeploy]
      exact TxStepAtHead.initL2 rfl rfl
    · by_cases h6 : n ≤ 6
      · obtain ⟨hR, hR'⟩ := staleHintRun_succ_of_le (n := n) (by omega) h6
        refine ⟨K.appender, .insert ((n : ℕ) : UInt256) (n - 1), ?_, ?_⟩
        · simp [staleHintTxAtHead, h0, h6]
        · rw [hR, hR']
          obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
          rw [Nat.add_sub_cancel]
          exact TxStepAtHead.insert rfl (stale_honest_checks k (by omega))
      · have h7 : n = 7 := by omega
        subst h7
        refine ⟨K.appender, .insert 7 0, rfl, ?_⟩
        show TxStepAtHead K (chainTree 6) K.appender (.insert 7 0) (chainTree 7)
        exact TxStepAtHead.insert rfl honest_insert_succeeds_at_head.2.2
  · left
    refine ⟨?_, ?_⟩
    · simp only [staleHintTxAtHead]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    · unfold staleHintRunAtHead
      rw [ite_eq_right (by omega), ite_eq_right (by omega), Nat.min_eq_right (by omega),
        Nat.min_eq_right (by omega)]

theorem staleHintRun_witness (K : Roles) :
    TxRunAtHead K staleHintRunAtHead (staleHintTxAtHead K)
      ∧ staleHintRunAtHead 0 = predeploy
      ∧ staleHintRunAtHead 8 = chainTree 7
      ∧ staleHintTxAtHead K 7 = some (K.appender, .insert 7 0)
      ∧ ¬ TxRun K staleHintRunAtHead (staleHintTxAtHead K)
      ∧ TxRun K staleHintRunAtHead (relabelAtHead staleHintRunAtHead (staleHintTxAtHead K))
      ∧ relabelAtHead staleHintRunAtHead (staleHintTxAtHead K) 7
          = some (K.appender, .insert 7 6) := by
  have hrun := staleHintRun_txRunAtHead K
  have h0 : staleHintRunAtHead 0 = predeploy := rfl
  have h7 : staleHintTxAtHead K 7 = some (K.appender, .insert 7 0) := rfl
  refine ⟨hrun, h0, rfl, h7, ?_, txRunAtHead_relabel hrun h0, ?_⟩
  · intro hpin
    have hs := runOf_some hpin h7
    obtain ⟨_, low, hch, _⟩ := txStep_insert_inv hs
    exact honest_insert_succeeds_at_head.2.1 low hch
  · have hR7 : staleHintRunAtHead 7 = chainTree 6 := rfl
    rw [(relabelAtHead_keeps_shape _ _ 7).2.2 K.appender 7 0 h7, hR7]
    have hl : landingAtHead (chainTree 6) 7 0 = 6 := by
      unfold landingAtHead
      rw [HonestInsertRevertsAtDeployedFuel.2.2.2.2.1]
      rfl
    rw [hl]

/-! ## The named statements -/

theorem WalkAtHeadIsLeafCountSearch : Properties.WalkAtHeadIsLeafCountSearch :=
  fun _ hV v hint low hi => walkAtHead_iff_leafCount hV v hint low hi

theorem WalkAtHeadTerminates : Properties.WalkAtHeadTerminates :=
  fun _ hV v hint hi => walkAtHead_terminates hV v hint hi

theorem WalkAtHeadDeterministic : Properties.WalkAtHeadDeterministic :=
  fun _ _ _ _ _ h h' => walkAtHead_det h h'

theorem InsertChecksAtHeadYieldGuard : Properties.InsertChecksAtHeadYieldGuard :=
  fun _ hV _ _ _ h => insertChecksAtHead_guard hV h

theorem InsertAtHeadLandingHintIndependent : Properties.InsertAtHeadLandingHintIndependent :=
  fun _ hV _ _ _ _ _ h h' => insertAtHead_landing_hint_independent hV h h'

theorem InsertAtHeadEnabledIff : Properties.InsertAtHeadEnabledIff :=
  fun _ hV v hint => insertAtHead_enabled_iff hV v hint

theorem InsertChecksAtHeadVsPin : Properties.InsertChecksAtHeadVsPin :=
  fun _ hV _ _ _ => ⟨insertChecksAtHead_of_pin, pin_insertChecks_of_atHead hV⟩

theorem HonestInsertSucceedsAtHead : Properties.HonestInsertSucceedsAtHead :=
  honest_insert_succeeds_at_head

theorem PinTxStepIsTxStepAtHead : Properties.PinTxStepIsTxStepAtHead :=
  fun _ _ _ _ _ h => pin_txStep_is_txStepAtHead h

theorem TxStepAtHeadIsRelabelledTxStep : Properties.TxStepAtHeadIsRelabelledTxStep :=
  fun _ _ _ _ _ hV h => txStepAtHead_relabel hV h

theorem RelabelAtHeadKeepsShape : Properties.RelabelAtHeadKeepsShape :=
  relabelAtHead_keeps_shape

theorem TxRunAtHeadIsRelabelledTxRun : Properties.TxRunAtHeadIsRelabelledTxRun :=
  fun _ _ _ hR h0 => txRunAtHead_relabel hR h0

theorem InitL2AtMostOnceAtHead : Properties.InitL2AtMostOnceAtHead :=
  initL2_at_most_once_at_head

theorem TxRunAtHeadAppendOnly : Properties.TxRunAtHeadAppendOnly := txRunAtHead_appendOnly

theorem TxRunAtHeadKeysMono : Properties.TxRunAtHeadKeysMono := txRunAtHead_keysMono

theorem TxRunAtHeadFromValidIsRun : Properties.TxRunAtHeadFromValidIsRun :=
  txRunAtHead_from_valid_is_run

theorem PredeployRunStatesAtHead : Properties.PredeployRunStatesAtHead :=
  fun K R tx hR h0 => PredeployRunStates K R (relabelAtHead R tx) (txRunAtHead_relabel hR h0) h0

theorem PredeployRunReclaimableIffAbsentAtHead :
    Properties.PredeployRunReclaimableIffAbsentAtHead :=
  fun K R tx hR h0 =>
    PredeployRunReclaimableIffAbsent K R (relabelAtHead R tx) (txRunAtHead_relabel hR h0) h0

theorem StoredLeavesAreLeafHashesAtHead : Properties.StoredLeavesAreLeafHashesAtHead :=
  fun K hl R tx L hR hL h0 =>
    StoredLeavesAreLeafHashes K hl R (relabelAtHead R tx) L (txRunAtHead_relabel hR h0) hL h0

theorem PredeployStoredRootExclusiveOrBreakAtHead :
    Properties.PredeployStoredRootExclusiveOrBreakAtHead :=
  fun K h z0 hl R tx L hR hL h0 =>
    PredeployStoredRootExclusiveOrBreak K h z0 hl R (relabelAtHead R tx) L
      (txRunAtHead_relabel hR h0) hL h0

theorem StaleHintRunWitnessAtHead : Properties.StaleHintRunWitnessAtHead :=
  staleHintRun_witness

end Contracts.InteropCommitmentTree
