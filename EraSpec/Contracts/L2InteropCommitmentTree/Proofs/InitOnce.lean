import EraSpec.Contracts.L2InteropCommitmentTree.Properties.InitOnce
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.HintSearch
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.RunHeight
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.Reaches
import EraSpec.Contracts.IndexedMerkleTree.Proofs.ResetAndZero

/-!
# Proofs: the tree is seeded once, and its history cannot be reset

Proofs of `EraSpec.Contracts.L2InteropCommitmentTree.Properties.InitOnce`. The run-level
results rest on two step facts: every successful transaction adds exactly one leaf, and
none changes the value at an index that was occupied before it (`initL2()` only runs on an
empty tree). The guardless machine keeps the second fact as long as index 0 holds value
zero, which each of its steps preserves. The leaf-level results rest on each step writing
`_nodes[0]` exactly where it changes a leaf, which needs the searched index to be in
bounds, which holds on the valid states a run from the predeploy goes through.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract AttackVectors.ResetAndZero

/-! ## The writes -/

@[simp] lemma setupWrites_leafCount (T : Tree) : (setupWrites T).leafCount = T.leafCount + 1 :=
  rfl

@[simp] lemma setupWrites_valueToIndex (T : Tree) :
    (setupWrites T).valueToIndex = T.valueToIndex :=
  rfl

lemma setupWrites_leaf (T : Tree) (i : ℕ) :
    (setupWrites T).leaf i = if i = 0 then ⟨0, 0, 0⟩ else T.leaf i :=
  rfl

/-- On the predeploy's zero storage, `IMT.setup`'s writes are the model's `setup`. -/
lemma setupWrites_predeploy : setupWrites predeploy = setup := by
  unfold setupWrites predeploy setup
  congr 1
  funext i
  split <;> rfl

lemma predeploy_not_initialized : ¬ Initialized predeploy := fun h => h rfl

lemma setup_initialized : Initialized setup := by
  show (1 : ℕ) ≠ 0
  omega

/-- `insert` leaves the value at every previously occupied index alone, whatever `low`. -/
lemma insert_value_old {T : Tree} {v : UInt256} {low i : ℕ} (hi : i < T.leafCount) :
    ((insert T v low).leaf i).value = (T.leaf i).value := by
  unfold insert
  dsimp only
  split_ifs with h1 h2
  · subst h1; rfl
  · omega
  · rfl

/-- `IMT.setup`'s writes leave every value alone when index 0 already holds value zero. -/
lemma setupWrites_value_old {T : Tree} (h0 : (T.leaf 0).value = 0) (i : ℕ) :
    ((setupWrites T).leaf i).value = (T.leaf i).value := by
  rw [setupWrites_leaf]
  split_ifs with h
  · subst h; exact h0.symm
  · rfl

/-- `insert` on an initialized tree keeps index 0's value. -/
lemma insert_value_zero {T : Tree} {v : UInt256} {low : ℕ} (hinit : Initialized T) :
    ((insert T v low).leaf 0).value = (T.leaf 0).value :=
  insert_value_old (Nat.pos_of_ne_zero hinit)

/-- The search exits at once when the hint's successor is not below `v`. -/
lemma lowSearch_exit {T : Tree} {v : UInt256} {i : ℕ}
    (h : ¬ ((T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v)) :
    ∀ fuel, lowSearch T v fuel i = some i
  | 0 => by simp only [lowSearch, h, ite_false]
  | _ + 1 => by simp only [lowSearch, h, ite_false]

/-- A guarded insert passes the contract's checks when its own low leaf is the hint. -/
lemma insertChecks_of_guard {T : Tree} {v : UInt256} {low : ℕ} (hg : InsertGuard T v low) :
    InsertChecks T v low low := by
  refine ⟨hg.initialized, hg.nonzero, hg.fresh, hg.inBounds, hg.lowBelow, ?_⟩
  apply lowSearch_exit
  rintro ⟨hne, hlt⟩
  rcases hg.window with h0 | hle
  · exact hne h0
  · exact absurd hle (not_le.mpr hlt)

/-- `insert(a, 0)` passes the contract's checks on `setup`. -/
lemma setup_insertChecks {a : UInt256} (ha : a ≠ 0) : InsertChecks setup a 0 0 :=
  insertChecks_of_guard (setup_insertGuard (Fin.pos_iff_ne_zero.mpr ha))

/-! ## Single transactions -/

lemma txStep_initL2_inv {K : Roles} {T U : Tree} {c : Caller} (h : TxStep K T c .initL2 U) :
    c = K.upgrader ∧ T.leafCount = 0 ∧ U = setupWrites T := by
  cases h with
  | initL2 hc hg => exact ⟨hc, hg, rfl⟩

lemma txStep_insert_inv {K : Roles} {T U : Tree} {c : Caller} {v : UInt256} {hint : ℕ}
    (h : TxStep K T c (.insert v hint) U) :
    c = K.appender ∧ ∃ low, InsertChecks T v hint low ∧ U = insert T v low := by
  cases h with
  | insert hc hch => exact ⟨hc, _, hch, rfl⟩

lemma txStep_leafCount {K : Roles} {T U : Tree} {c : Caller} {call : Call}
    (h : TxStep K T c call U) : U.leafCount = T.leafCount + 1 := by
  cases h <;> rfl

lemma txStep_value_old {K : Roles} {T U : Tree} {c : Caller} {call : Call}
    (h : TxStep K T c call U) : ∀ i < T.leafCount, (U.leaf i).value = (T.leaf i).value := by
  cases h with
  | initL2 _ hg => intro i hi; omega
  | insert _ _ => intro i hi; exact insert_value_old hi

theorem initL2_on_predeploy (K : Roles) (c : Caller) (U : Tree) :
    TxStep K predeploy c .initL2 U ↔ c = K.upgrader ∧ U = setup := by
  constructor
  · intro h
    obtain ⟨hc, _, hU⟩ := txStep_initL2_inv h
    exact ⟨hc, hU.trans setupWrites_predeploy⟩
  · rintro ⟨rfl, rfl⟩
    rw [← setupWrites_predeploy]
    exact TxStep.initL2 rfl rfl

theorem initL2_reverts_once_initialized (K : Roles) (T : Tree) (c : Caller) (U : Tree)
    (hinit : Initialized T) : ¬ TxStep K T c .initL2 U :=
  fun h => hinit (txStep_initL2_inv h).2.1

theorem insert_reverts_before_init (K : Roles) (T : Tree) (c : Caller) (v : UInt256) (hint : ℕ)
    (U : Tree) (hinit : ¬ Initialized T) : ¬ TxStep K T c (.insert v hint) U := by
  intro h
  obtain ⟨_, _, hch, _⟩ := txStep_insert_inv h
  exact hinit hch.initialized

theorem txStep_caller_is_role (K : Roles) (T : Tree) (c : Caller) (call : Call) (U : Tree)
    (h : TxStep K T c call U) : c = K.roleFor call := by
  cases h with
  | initL2 hc _ => exact hc
  | insert hc _ => exact hc

/-- On a valid tree, a successful transaction is a guarded insert at the searched index. -/
lemma txStep_of_valid {K : Roles} {T U : Tree} {c : Caller} {call : Call} (hV : Valid T)
    (h : TxStep K T c call U) : ∃ v low, InsertGuard T v low ∧ U = insert T v low := by
  cases h with
  | initL2 _ hg => exact absurd hg (Nat.pos_iff_ne_zero.mp hV.occupied)
  | insert _ hch =>
    exact ⟨_, _, search_yields_guard hV hch.initialized hch.nonzero hch.unregistered
      hch.hintInBounds hch.hintBelow hch.search, rfl⟩

/-! ## Runs: generic facts -/

lemma runOf_some {step : Tree → Caller → Call → Tree → Prop} {R : ℕ → Tree}
    {tx : Trace} (hR : RunOf step R tx) {n : ℕ} {c : Caller} {call : Call}
    (h : tx n = some (c, call)) : step (R n) c call (R (n + 1)) := by
  rcases hR n with ⟨hn, _⟩ | ⟨c', call', hn, hs⟩
  · rw [h] at hn; exact absurd hn (by simp)
  · rw [h] at hn
    simp only [Option.some.injEq, Prod.mk.injEq] at hn
    obtain ⟨rfl, rfl⟩ := hn
    exact hs

lemma runOf_none {step : Tree → Caller → Call → Tree → Prop} {R : ℕ → Tree}
    {tx : Trace} (hR : RunOf step R tx) {n : ℕ} (h : tx n = none) :
    R (n + 1) = R n := by
  rcases hR n with ⟨_, he⟩ | ⟨c', call', hn, _⟩
  · exact he
  · rw [h] at hn; exact absurd hn (by simp)

/-- The tail of a run from step `k` is a run. -/
lemma runOf_shift {step : Tree → Caller → Call → Tree → Prop} {R : ℕ → Tree}
    {tx : Trace} (hR : RunOf step R tx) (k : ℕ) :
    RunOf step (fun n => R (k + n)) (fun n => tx (k + n)) :=
  fun n => hR (k + n)

/-- Step-wise append-only gives append-only over any stretch. -/
lemma appendOnly_of_steps {R : ℕ → Tree}
    (hstep : ∀ n, (R n).leafCount ≤ (R (n + 1)).leafCount
      ∧ ∀ i < (R n).leafCount, ((R (n + 1)).leaf i).value = ((R n).leaf i).value)
    {m n : ℕ} (hmn : m ≤ n) :
    (R m).leafCount ≤ (R n).leafCount
      ∧ ∀ i < (R m).leafCount, ((R n).leaf i).value = ((R m).leaf i).value := by
  induction n, hmn using Nat.le_induction with
  | base => exact ⟨le_rfl, fun _ _ => rfl⟩
  | succ n _ ih =>
    obtain ⟨hc, hv⟩ := ih
    obtain ⟨hc', hv'⟩ := hstep n
    refine ⟨hc.trans hc', fun i hi => ?_⟩
    rw [hv' i (lt_of_lt_of_le hi hc), hv i hi]

/-- Append-only keeps every key. -/
lemma keys_subset_of_appendOnly {T U : Tree} (hc : T.leafCount ≤ U.leafCount)
    (hv : ∀ i < T.leafCount, (U.leaf i).value = (T.leaf i).value) :
    keys (toAbs T) ⊆ keys (toAbs U) := by
  intro x hx
  obtain ⟨i, hi, hval⟩ := mem_keys_iff_index.mp hx
  exact mem_keys_iff_index.mpr ⟨i, lt_of_lt_of_le hi hc, by rw [hv i hi, hval]⟩

/-- A history whose key set never shrinks has no stretch equal to `resetHistory a`. -/
lemma not_resetHistory_of_keysMono {R : ℕ → Tree} {a : UInt256} (ha : a ≠ 0)
    (hmono : ∀ m n, m ≤ n → keys (toAbs (R m)) ⊆ keys (toAbs (R n))) (k : ℕ) :
    ¬ ∀ n, toAbs (R (k + n)) = resetHistory a n := by
  intro h
  have h1 : a ∈ keys (toAbs (R (k + 1))) := by rw [h 1]; exact resetHistory_delivers a
  have h2 : a ∉ keys (toAbs (R (k + 2))) := by rw [h 2]; exact resetHistory_forgets ha
  exact h2 (hmono (k + 1) (k + 2) (by omega) h1)

/-! ## Runs of the deployed contract -/

lemma txRun_step_appendOnly {K : Roles} {R : ℕ → Tree} {tx : Trace}
    (hR : TxRun K R tx) (n : ℕ) :
    (R n).leafCount ≤ (R (n + 1)).leafCount
      ∧ ∀ i < (R n).leafCount, ((R (n + 1)).leaf i).value = ((R n).leaf i).value := by
  rcases hR n with ⟨_, he⟩ | ⟨c, call, _, hs⟩
  · rw [he]; exact ⟨le_rfl, fun _ _ => rfl⟩
  · exact ⟨by rw [txStep_leafCount hs]; omega, txStep_value_old hs⟩

theorem txRun_appendOnly (K : Roles) (R : ℕ → Tree) (tx : Trace)
    (hR : TxRun K R tx) (m n : ℕ) (hmn : m ≤ n) :
    (R m).leafCount ≤ (R n).leafCount
      ∧ ∀ i < (R m).leafCount, ((R n).leaf i).value = ((R m).leaf i).value :=
  appendOnly_of_steps (txRun_step_appendOnly hR) hmn

theorem txRun_keysMono (K : Roles) (R : ℕ → Tree) (tx : Trace)
    (hR : TxRun K R tx) (m n : ℕ) (hmn : m ≤ n) :
    keys (toAbs (R m)) ⊆ keys (toAbs (R n)) :=
  keys_subset_of_appendOnly (txRun_appendOnly K R tx hR m n hmn).1
    (txRun_appendOnly K R tx hR m n hmn).2

theorem resetHistory_unreachable (K : Roles) (R : ℕ → Tree) (tx : Trace)
    (a : UInt256) (ha : a ≠ 0) (hR : TxRun K R tx) (k : ℕ) :
    ¬ ∀ n : ℕ, toAbs (R (k + n)) = resetHistory a n :=
  not_resetHistory_of_keysMono ha (txRun_keysMono K R tx hR) k

theorem initL2_at_most_once (K : Roles) (R : ℕ → Tree) (tx : Trace)
    (hR : TxRun K R tx) (m n : ℕ) (cm cn : Caller) (hm : tx m = some (cm, .initL2))
    (hn : tx n = some (cn, .initL2)) : m = n := by
  have sm := runOf_some hR hm
  have sn := runOf_some hR hn
  have hm0 := (txStep_initL2_inv sm).2.1
  have hn0 := (txStep_initL2_inv sn).2.1
  have hm1 := txStep_leafCount sm
  have hn1 := txStep_leafCount sn
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := (txRun_appendOnly K R tx hR (m + 1) n hlt).1
    omega
  · have := (txRun_appendOnly K R tx hR (n + 1) m hlt).1
    omega

theorem noInitL2_once_initialized (K : Roles) (R : ℕ → Tree) (tx : Trace)
    (hR : TxRun K R tx) (m n : ℕ) (hmn : m ≤ n) (hinit : Initialized (R m)) (c : Caller) :
    tx n ≠ some (c, .initL2) := by
  intro hn
  have hn0 := (txStep_initL2_inv (runOf_some hR hn)).2.1
  have := (txRun_appendOnly K R tx hR m n hmn).1
  unfold Initialized at hinit
  omega

theorem noRun_from_setup_reinitializes (K : Roles) (R : ℕ → Tree)
    (tx : Trace) (hR : TxRun K R tx) (h0 : R 0 = setup) (n : ℕ)
    (c : Caller) : tx n ≠ some (c, .initL2) :=
  noInitL2_once_initialized K R tx hR 0 n (Nat.zero_le n) (by rw [h0]; exact setup_initialized) c

theorem txRun_from_valid_is_run (K : Roles) (R : ℕ → Tree) (tx : Trace)
    (hR : TxRun K R tx) (h0 : Valid (R 0)) : Run R := by
  have hval : ∀ n, Valid (R n) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      rcases hR n with ⟨_, he⟩ | ⟨c, call, _, hs⟩
      · rw [he]; exact ih
      · obtain ⟨v, low, hg, hU⟩ := txStep_of_valid ih hs
        rw [hU]
        exact insert_preserves_valid ih hg
  intro n
  rcases hR n with ⟨_, he⟩ | ⟨c, call, _, hs⟩
  · exact Or.inl he
  · exact Or.inr (txStep_of_valid (hval n) hs)

theorem run_lifts_to_txRun (K : Roles) (R : ℕ → Tree) (hR : Run R) (h0 : R 0 = setup) :
    ∃ (R' : ℕ → Tree) (tx : Trace), TxRun K R' tx ∧ R' 0 = predeploy
      ∧ tx 0 = some (K.upgrader, .initL2) ∧ ∀ n : ℕ, R' (n + 1) = R n := by
  have hchoice : ∀ n, ∃ o : Option (Caller × Call), (o = none ∧ R (n + 1) = R n)
      ∨ ∃ (c : Caller) (call : Call), o = some (c, call) ∧ TxStep K (R n) c call (R (n + 1)) := by
    intro n
    rcases hR n with he | ⟨v, low, hg, he⟩
    · exact ⟨none, Or.inl ⟨rfl, he⟩⟩
    · refine ⟨some (K.appender, .insert v low), Or.inr ⟨_, _, rfl, ?_⟩⟩
      rw [he]
      exact TxStep.insert rfl (insertChecks_of_guard hg)
  choose o ho using hchoice
  refine ⟨fun n => match n with | 0 => predeploy | n + 1 => R n,
    fun n => match n with | 0 => some (K.upgrader, .initL2) | n + 1 => o n, ?_, rfl, rfl,
    fun _ => rfl⟩
  intro n
  match n with
  | 0 =>
    refine Or.inr ⟨K.upgrader, .initL2, rfl, ?_⟩
    show TxStep K predeploy K.upgrader .initL2 (R 0)
    rw [h0, ← setupWrites_predeploy]
    exact TxStep.initL2 rfl rfl
  | n + 1 => exact ho n

/-- A run's states stay on the predeploy while no transaction has succeeded. -/
lemma txRun_stays_predeploy {K : Roles} {R : ℕ → Tree} {tx : Trace}
    (hR : TxRun K R tx) (h0 : R 0 = predeploy) :
    ∀ n, (∀ j < n, tx j = none) → R n = predeploy := by
  intro n
  induction n with
  | zero => intro _; exact h0
  | succ n ih =>
    intro hj
    rw [runOf_none hR (hj n (Nat.lt_succ_self n))]
    exact ih (fun j hjn => hj j (Nat.lt_succ_of_lt hjn))

theorem predeploy_run_shape (K : Roles) (R : ℕ → Tree) (tx : Trace)
    (hR : TxRun K R tx) (h0 : R 0 = predeploy) :
    (∀ n : ℕ, R n = predeploy ∧ tx n = none)
    ∨ ∃ k : ℕ, (∀ n ≤ k, R n = predeploy) ∧ (∀ n < k, tx n = none)
        ∧ tx k = some (K.upgrader, .initL2) ∧ R (k + 1) = setup
        ∧ Run (fun n => R (k + 1 + n)) := by
  classical
  have hstay := txRun_stays_predeploy hR h0
  by_cases hall : ∀ n, tx n = none
  · exact Or.inl fun n => ⟨hstay n (fun j _ => hall j), hall n⟩
  · right
    replace hall : ∃ n, tx n ≠ none := not_forall.mp hall
    have hk : tx (Nat.find hall) ≠ none := Nat.find_spec hall
    have hbefore : ∀ n < Nat.find hall, tx n = none := fun n hn =>
      not_not.mp (Nat.find_min hall hn)
    have hRk : R (Nat.find hall) = predeploy := hstay _ hbefore
    obtain ⟨⟨c, call⟩, hck⟩ := Option.ne_none_iff_exists'.mp hk
    have hs := runOf_some hR hck
    rw [hRk] at hs
    cases call with
    | insert v hint =>
      exact absurd hs (insert_reverts_before_init K _ c v hint _ predeploy_not_initialized)
    | initL2 =>
      obtain ⟨hc, _, hU⟩ := txStep_initL2_inv hs
      have hR1 : R (Nat.find hall + 1) = setup := hU.trans setupWrites_predeploy
      refine ⟨Nat.find hall, fun n hn => hstay n (fun j hj => hbefore j (by omega)), hbefore,
        by rw [hck, hc], hR1, ?_⟩
      exact txRun_from_valid_is_run K _ _ (runOf_shift hR (Nat.find hall + 1))
        (by show Valid (R (Nat.find hall + 1 + 0)); rw [Nat.add_zero, hR1]; exact setup_valid)

/-- A `Run` reaches each of its states from its first. -/
lemma run_reaches {S : ℕ → Tree} (hS : Run S) : ∀ j, Reaches (S 0) (S j)
  | 0 => .refl
  | j + 1 => by
    rcases hS j with he | ⟨v, low, hg, he⟩
    · rw [he]; exact run_reaches hS j
    · rw [he]; exact .tail (run_reaches hS j) hg

lemma hSetup_eq_lift :
    (⟨setup, ⟨setup.leafCount, fmHeight setup.leafCount⟩⟩ : HState) = hSetup := by
  unfold hSetup
  rw [setupDims_eq]
  rfl

theorem predeploy_run_states (K : Roles) (R : ℕ → Tree) (tx : Trace)
    (hR : TxRun K R tx) (h0 : R 0 = predeploy) (n : ℕ) :
    R n = predeploy
      ∨ (Reaches setup (R n) ∧ Valid (R n)
          ∧ HReaches hSetup ⟨R n, ⟨(R n).leafCount, fmHeight (R n).leafCount⟩⟩) := by
  rcases predeploy_run_shape K R tx hR h0 with hall | ⟨k, hpre, _, _, hR1, hrun⟩
  · exact Or.inl (hall n).1
  · by_cases hn : n ≤ k
    · exact Or.inl (hpre n hn)
    · right
      obtain ⟨j, rfl⟩ : ∃ j, n = k + 1 + j := ⟨n - (k + 1), by omega⟩
      have hreach : Reaches setup (R (k + 1 + j)) := by
        have := run_reaches hrun j
        simp only [Nat.add_zero] at this
        rw [hR1] at this
        exact this
      refine ⟨hreach, reaches_valid hreach setup_valid, ?_⟩
      have := reaches_lifts hreach
      rw [hSetup_eq_lift] at this
      exact this

theorem predeploy_run_reclaimable_iff_absent (K : Roles) (R : ℕ → Tree)
    (tx : Trace) (hR : TxRun K R tx) (h0 : R 0 = predeploy) (n : ℕ)
    (v : UInt256) (hinit : Initialized (R n)) (hv : v ≠ 0) :
    (∃ W ∈ toAbs (R n), W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))
      ↔ v ∉ keys (toAbs (R n)) := by
  rcases predeploy_run_shape K R tx hR h0 with hall | ⟨k, hpre, _, _, hR1, hrun⟩
  · exact absurd ((hall n).1 ▸ hinit) predeploy_not_initialized
  · by_cases hn : n ≤ k
    · exact absurd ((hpre n hn) ▸ hinit) predeploy_not_initialized
    · obtain ⟨j, rfl⟩ : ∃ j, n = k + 1 + j := ⟨n - (k + 1), by omega⟩
      exact genesis_run_reclaimable_iff_absent hrun (by simp only [Nat.add_zero]; exact hR1) j v hv

/-! ## Anti-vacuity -/

lemma genesisRun_txRun (K : Roles) {a b : UInt256} (ha : 0 < a) (hab : a < b) :
    TxRun K (genesisRun a b) (genesisTx K a b) := by
  obtain ⟨hg1, hg2⟩ := threeLeafTree_guards ha hab
  intro n
  match n with
  | 0 =>
    refine Or.inr ⟨K.upgrader, .initL2, rfl, ?_⟩
    show TxStep K predeploy K.upgrader .initL2 setup
    rw [← setupWrites_predeploy]
    exact TxStep.initL2 rfl rfl
  | 1 =>
    refine Or.inr ⟨K.appender, .insert a 0, rfl, ?_⟩
    show TxStep K setup K.appender (.insert a 0) (insert setup a 0)
    exact TxStep.insert rfl (insertChecks_of_guard hg1)
  | 2 =>
    refine Or.inr ⟨K.appender, .insert b 1, rfl, ?_⟩
    show TxStep K (insert setup a 0) K.appender (.insert b 1) (insert (insert setup a 0) b 1)
    exact TxStep.insert rfl (insertChecks_of_guard hg2)
  | n + 3 => exact Or.inl ⟨rfl, rfl⟩

theorem genesisRun_witness :
    deployedRoles.upgrader ≠ deployedRoles.appender ∧
    ∀ (K : Roles) (a b : UInt256), 0 < a → a < b →
      TxRun K (genesisRun a b) (genesisTx K a b) ∧ genesisRun a b 0 = predeploy
        ∧ genesisTx K a b 0 = some (K.upgrader, .initL2)
        ∧ genesisTx K a b 1 = some (K.appender, .insert a 0)
        ∧ genesisTx K a b 2 = some (K.appender, .insert b 1)
        ∧ ¬ Initialized (genesisRun a b 0)
        ∧ genesisRun a b 1 = setup ∧ Initialized (genesisRun a b 1)
        ∧ genesisRun a b 3 = threeLeafTree a b ∧ Initialized (genesisRun a b 3)
        ∧ a ∈ keys (toAbs (genesisRun a b 3)) ∧ b ∈ keys (toAbs (genesisRun a b 3))
        ∧ TxRun K (fun n => genesisRun a b (n + 1)) (fun n => genesisTx K a b (n + 1))
        ∧ Valid (genesisRun a b 1) ∧ Run (fun n => genesisRun a b (n + 1))
        ∧ ¬ (∃ U : Tree, TxStep K (genesisRun a b 1) K.upgrader .initL2 U) := by
  refine ⟨by decide, fun K a b ha hab => ?_⟩
  have hrun := genesisRun_txRun K ha hab
  have htail : TxRun K (fun n => genesisRun a b (n + 1)) (fun n => genesisTx K a b (n + 1)) :=
    fun n => by simpa only [Nat.add_comm n 1] using hrun (n + 1)
  have hv1 : Valid (genesisRun a b 1) := setup_valid
  have hc3 : (genesisRun a b 3).leafCount = 3 := rfl
  refine ⟨hrun, rfl, rfl, rfl, rfl, predeploy_not_initialized, rfl, setup_initialized, rfl,
    ?_, mem_keys_iff_index.mpr ⟨1, by rw [hc3]; omega, rfl⟩,
    mem_keys_iff_index.mpr ⟨2, by rw [hc3]; omega, rfl⟩, htail, hv1,
    txRun_from_valid_is_run K _ _ htail hv1, ?_⟩
  · show (genesisRun a b 3).leafCount ≠ 0
    rw [hc3]; omega
  · rintro ⟨U, hU⟩
    exact initL2_reverts_once_initialized K _ _ _ setup_initialized hU

/-! ## The guard deleted -/

lemma txStepNoGuard_value_zero {K : Roles} {T U : Tree} {c : Caller} {call : Call}
    (h : TxStepNoGuard K T c call U) (h0 : (T.leaf 0).value = 0) : (U.leaf 0).value = 0 := by
  cases h with
  | initL2 _ => rfl
  | insert _ hch => rw [insert_value_zero hch.initialized]; exact h0

lemma txStepNoGuard_appendOnly {K : Roles} {T U : Tree} {c : Caller} {call : Call}
    (h : TxStepNoGuard K T c call U) (h0 : (T.leaf 0).value = 0) :
    T.leafCount ≤ U.leafCount ∧ ∀ i < T.leafCount, (U.leaf i).value = (T.leaf i).value := by
  cases h with
  | initL2 _ => exact ⟨by simp, fun i _ => setupWrites_value_old h0 i⟩
  | insert _ _ => exact ⟨by simp [insert], fun i hi => insert_value_old hi⟩

lemma txRunNoGuard_value_zero {K : Roles} {R : ℕ → Tree} {tx : Trace}
    (hR : TxRunNoGuard K R tx) (h0 : ((R 0).leaf 0).value = 0) :
    ∀ n, ((R n).leaf 0).value = 0 := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    rcases hR n with ⟨_, he⟩ | ⟨c, call, _, hs⟩
    · rw [he]; exact ih
    · exact txStepNoGuard_value_zero hs ih

theorem guardless_runs_keep_keys (K : Roles) (R : ℕ → Tree) (tx : Trace)
    (hR : TxRunNoGuard K R tx) (h0 : ((R 0).leaf 0).value = 0) (m n : ℕ) (hmn : m ≤ n) :
    keys (toAbs (R m)) ⊆ keys (toAbs (R n)) := by
  have hstep : ∀ n, (R n).leafCount ≤ (R (n + 1)).leafCount
      ∧ ∀ i < (R n).leafCount, ((R (n + 1)).leaf i).value = ((R n).leaf i).value := by
    intro n
    rcases hR n with ⟨_, he⟩ | ⟨c, call, _, hs⟩
    · rw [he]; exact ⟨le_rfl, fun _ _ => rfl⟩
    · exact txStepNoGuard_appendOnly hs (txRunNoGuard_value_zero hR h0 n)
  obtain ⟨hc, hv⟩ := appendOnly_of_steps hstep hmn
  exact keys_subset_of_appendOnly hc hv

theorem guardless_resetHistory_unreachable (K : Roles) (R : ℕ → Tree)
    (tx : Trace) (a : UInt256) (ha : a ≠ 0) (hR : TxRunNoGuard K R tx)
    (h0 : ((R 0).leaf 0).value = 0) (k : ℕ) :
    ¬ ∀ n : ℕ, toAbs (R (k + n)) = resetHistory a n :=
  not_resetHistory_of_keysMono ha (guardless_runs_keep_keys K R tx hR h0) k

/-- Every leaf after the second `initL2()` has no successor. -/
private lemma reinitRun_three_nextKey {a : UInt256} :
    ∀ X ∈ toAbs (reinitRun a 3), X.nextKey = 0 := by
  intro X hX
  obtain ⟨i, hi, _, hnv⟩ := mem_toAbs.mp hX
  rw [← hnv]
  have hi3 : i < 3 := hi
  interval_cases i <;> rfl

/-- A history step into a set whose leaves all have no successor, from a set holding a leaf
with a successor, is neither idle nor an `imtInsert` through a leaf strictly below the
inserted value. -/
private lemma not_step_into_terminal {s t : Finset AbsLeaf} (ht : ∀ X ∈ t, X.nextKey = 0)
    {L : AbsLeaf} (hL : L ∈ s) (hLn : L.nextKey ≠ 0) :
    t ≠ s ∧ ∀ (W : AbsLeaf) (v : UInt256), W.key < v → t ≠ imtInsert s W v := by
  refine ⟨fun h => hLn (ht L (h ▸ hL)), fun W v hlt h => ?_⟩
  have hmem : (⟨W.key, v⟩ : AbsLeaf) ∈ t := by
    rw [h]; exact Finset.mem_insert_self _ _
  have hv : v = 0 := ht _ hmem
  rw [hv] at hlt
  exact absurd hlt (Fin.not_lt_zero _)

theorem guardless_reinit_breaks_exclusivity (K : Roles) (a : UInt256) (ha : a ≠ 0) :
    TxRunNoGuard K (reinitRun a) (reinitTx K a) ∧ reinitRun a 0 = predeploy
      ∧ ((reinitRun a 0).leaf 0).value = 0
      ∧ reinitTx K a 0 = some (K.upgrader, .initL2)
      ∧ reinitTx K a 1 = some (K.appender, .insert a 0)
      ∧ reinitTx K a 2 = some (K.upgrader, .initL2)
      ∧ reinitRun a 1 = setup ∧ reinitRun a 2 = insert setup a 0
      ∧ ¬ (∃ U : Tree, TxStep K (reinitRun a 2) K.upgrader .initL2 U)
      ∧ Initialized (reinitRun a 3) ∧ (reinitRun a 3).leafCount = 3
      ∧ (reinitRun a 3).leaf 0 = ⟨0, 0, 0⟩ ∧ (reinitRun a 3).leaf 1 = ⟨a, 0, 0⟩
      ∧ (reinitRun a 3).leaf 2 = ⟨0, 0, 0⟩
      ∧ (reinitRun a 3).valueToIndex a = 1
      ∧ a ∈ keys (toAbs (reinitRun a 3))
      ∧ (∃ W ∈ toAbs (reinitRun a 3), W.key < a ∧ (W.nextKey = 0 ∨ a < W.nextKey))
      ∧ ¬ ((∃ W ∈ toAbs (reinitRun a 3), W.key < a ∧ (W.nextKey = 0 ∨ a < W.nextKey))
            ↔ a ∉ keys (toAbs (reinitRun a 3)))
      ∧ ¬ Valid (reinitRun a 3)
      ∧ ¬ Evolution (fun n => toAbs (reinitRun a (n + 1)))
      ∧ ¬ GuardedEvolution (fun n => toAbs (reinitRun a (n + 1))) := by
  have hpos : (0 : UInt256) < a := Fin.pos_iff_ne_zero.mpr ha
  -- the run
  have hrun : TxRunNoGuard K (reinitRun a) (reinitTx K a) := by
    intro n
    match n with
    | 0 =>
      refine Or.inr ⟨K.upgrader, .initL2, rfl, ?_⟩
      show TxStepNoGuard K predeploy K.upgrader .initL2 setup
      rw [← setupWrites_predeploy]
      exact TxStepNoGuard.initL2 rfl
    | 1 =>
      refine Or.inr ⟨K.appender, .insert a 0, rfl, ?_⟩
      show TxStepNoGuard K setup K.appender (.insert a 0) (insert setup a 0)
      exact TxStepNoGuard.insert rfl (setup_insertChecks ha)
    | 2 =>
      refine Or.inr ⟨K.upgrader, .initL2, rfl, ?_⟩
      show TxStepNoGuard K (insert setup a 0) K.upgrader .initL2 (setupWrites (insert setup a 0))
      exact TxStepNoGuard.initL2 rfl
    | n + 3 => exact Or.inl ⟨rfl, rfl⟩
  have hc2 : (reinitRun a 2).leafCount = 2 := rfl
  have hc3 : (reinitRun a 3).leafCount = 3 := rfl
  -- the delivered value is still a key
  have hkey : a ∈ keys (toAbs (reinitRun a 3)) :=
    mem_keys_iff_index.mpr ⟨1, by rw [hc3]; omega, rfl⟩
  -- the reset sentinel straddles it
  have hW : ∃ W ∈ toAbs (reinitRun a 3), W.key < a ∧ (W.nextKey = 0 ∨ a < W.nextKey) :=
    ⟨⟨0, 0⟩, mem_toAbs.mpr ⟨0, by rw [hc3]; omega, rfl, rfl⟩, hpos, Or.inl rfl⟩
  -- the sentinel of the previous state has a successor
  have hL : (⟨0, a⟩ : AbsLeaf) ∈ toAbs (reinitRun a 2) :=
    mem_toAbs.mpr ⟨0, by rw [hc2]; omega, rfl, rfl⟩
  obtain ⟨hne, hnins⟩ := not_step_into_terminal (reinitRun_three_nextKey (a := a)) hL ha
  refine ⟨hrun, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, ?_, hkey, hW,
    fun hiff => hiff.mp hW hkey, ?_, ?_, ?_⟩
  · rintro ⟨U, hU⟩
    exact initL2_reverts_once_initialized K _ _ _
      (by show (reinitRun a 2).leafCount ≠ 0; rw [hc2]; omega) hU
  · show (reinitRun a 3).leafCount ≠ 0
    rw [hc3]; omega
  · show (insert setup a 0).valueToIndex a = 1
    simp [insert, setup]
  · intro hV
    have := hV.idxInj 0 (by rw [hc3]; omega) 2 (by rw [hc3]; omega) rfl
    omega
  · intro hevo
    rcases hevo 1 with h | ⟨W₀, v, _, hlt, _, h⟩
    · exact hne h
    · exact hnins W₀ v hlt h
  · intro hge
    rcases hge 1 with h | ⟨W₀, v, _, hlt, _, _, h⟩
    · exact hne h
    · exact hnins W₀ v hlt h

/-! ## The hash tree's leaf level -/

section LeafLevel

open MerkleSpec MerkleSpec.Verifier

lemma levelWrites_insert {hl : LeafHash} {T : Tree} {H : LeafLevel} {v : UInt256}
    {hint low : ℕ} (hch : InsertChecks T v hint low) :
    levelWrites hl T H (.insert v hint) = insertLevel hl T H v low := by
  simp only [levelWrites, hch.search]

lemma levelRun_some {hl : LeafHash} {R : ℕ → Tree} {tx : Trace} {L : ℕ → LeafLevel}
    (hL : LevelRun hl R tx L) {n : ℕ} {c : Caller} {call : Call} (h : tx n = some (c, call)) :
    L (n + 1) = levelWrites hl (R n) (L n) call := by
  have := hL n
  rw [h] at this
  exact this

lemma levelRun_none {hl : LeafHash} {R : ℕ → Tree} {tx : Trace} {L : ℕ → LeafLevel}
    (hL : LevelRun hl R tx L) {n : ℕ} (h : tx n = none) : L (n + 1) = L n := by
  have := hL n
  rw [h] at this
  exact this

/-- `initL2()` on an empty tree leaves the stored and list copies agreeing. -/
lemma agrees_setupWrites {hl : LeafHash} {T : Tree} {H : LeafLevel} (h0 : T.leafCount = 0) :
    ∀ i < (setupWrites T).leafCount, setupLevel hl T H i = hl ((setupWrites T).leaf i) := by
  intro i hi
  rw [setupWrites_leafCount, h0] at hi
  obtain rfl : i = 0 := by omega
  show setupLevel hl T H 0 = hl ⟨0, 0, 0⟩
  unfold setupLevel
  rw [h0, Function.update_self]

/-- An in-bounds `insert` keeps the stored and list copies agreeing. -/
lemma agrees_insert {hl : LeafHash} {T : Tree} {H : LeafLevel} {v : UInt256} {low : ℕ}
    (hag : ∀ i < T.leafCount, H i = hl (T.leaf i)) (hlow : low < T.leafCount) :
    ∀ i < (insert T v low).leafCount, insertLevel hl T H v low i = hl ((insert T v low).leaf i) := by
  intro i hi
  have hi' : i < T.leafCount + 1 := hi
  unfold insertLevel
  by_cases hn : i = T.leafCount
  · subst hn
    rw [Function.update_self, insert_leaf_new hlow]
  · rw [Function.update_of_ne hn]
    by_cases hlo : i = low
    · subst hlo
      rw [Function.update_self, insert_leaf_low]
    · rw [Function.update_of_ne hlo, insert_leaf_other hlo hn]
      exact hag i (by omega)

lemma storedLeaves_of_agrees {hl : LeafHash} {T : Tree} {H : LeafLevel}
    (hag : ∀ i < T.leafCount, H i = hl (T.leaf i)) :
    storedLeaves H T.leafCount = leafHashes hl T := by
  unfold storedLeaves leafHashes
  exact List.map_congr_left fun i hi => hag i (List.mem_range.mp hi)

/-- A state of a run from the predeploy that is initialized is valid. -/
lemma predeploy_run_valid {K : Roles} {R : ℕ → Tree} {tx : Trace} (hR : TxRun K R tx)
    (h0 : R 0 = predeploy) {n : ℕ} (hinit : Initialized (R n)) : Valid (R n) := by
  rcases predeploy_run_states K R tx hR h0 n with hp | ⟨_, hV, _⟩
  · exact absurd (hp ▸ hinit) predeploy_not_initialized
  · exact hV

theorem txRun_level_agrees (K : Roles) (hl : LeafHash) (R : ℕ → Tree) (tx : Trace)
    (L : ℕ → LeafLevel) (hR : TxRun K R tx) (hL : LevelRun hl R tx L) (h0 : R 0 = predeploy) :
    ∀ n, ∀ i < (R n).leafCount, L n i = hl ((R n).leaf i) := by
  intro n
  induction n with
  | zero => intro i hi; rw [h0] at hi; exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    rcases hR n with ⟨hn, he⟩ | ⟨c, call, hn, hs⟩
    · rw [he, levelRun_none hL hn]; exact ih
    · rw [levelRun_some hL hn]
      cases call with
      | initL2 =>
        obtain ⟨_, hc0, hU⟩ := txStep_initL2_inv hs
        rw [hU]
        exact agrees_setupWrites hc0
      | insert v hint =>
        obtain ⟨_, low, hch, hU⟩ := txStep_insert_inv hs
        rw [hU, levelWrites_insert hch]
        have hV := predeploy_run_valid hR h0 hch.initialized
        exact agrees_insert ih (search_yields_guard hV hch.initialized hch.nonzero
          hch.unregistered hch.hintInBounds hch.hintBelow hch.search).inBounds

theorem stored_leaves_are_leafHashes (K : Roles) (hl : LeafHash) (R : ℕ → Tree) (tx : Trace)
    (L : ℕ → LeafLevel) (hR : TxRun K R tx) (hL : LevelRun hl R tx L) (h0 : R 0 = predeploy)
    (n : ℕ) : storedLeaves (L n) (R n).leafCount = leafHashes hl (R n) :=
  storedLeaves_of_agrees (txRun_level_agrees K hl R tx L hR hL h0 n)

theorem predeploy_stored_root_exclusive_or_break (K : Roles) (h : Hash) (z0 : UInt256)
    (hl : LeafHash) (R : ℕ → Tree) (tx : Trace) (L : ℕ → LeafLevel) (hR : TxRun K R tx)
    (hL : LevelRun hl R tx L) (h0 : R 0 = predeploy) (n height : ℕ) (v : UInt256)
    (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256) (k₁ k₂ : ℕ) (hinit : Initialized (R n))
    (hI : InclusionAccepted h hl (rootOf h z0 (storedLeaves (L n) (R n).leafCount) height)
      v ℓ₁ i₁ s₁ k₁)
    (hN : NonInclusionAccepted h hl (rootOf h z0 (storedLeaves (L n) (R n).leafCount) height)
      v ℓ₂ i₂ s₂ k₂) :
    TreeRootBreak h z0 hl (R n) height s₁ k₁ i₁ ℓ₁
      ∨ TreeRootBreak h z0 hl (R n) height s₂ k₂ i₂ ℓ₂ := by
  rw [stored_leaves_are_leafHashes K hl R tx L hR hL h0 n] at hI hN
  exact proofs_exclusive_or_break (predeploy_run_valid hR h0 hinit) hI hN

/-- The honest path of index `j` of the stored tree is accepted against its fold. -/
lemma stored_path_accepts {h : Hash} {z0 : UInt256} (L : List UInt256) {height j : ℕ}
    (hj : j < 2 ^ height) {x : UInt256} (hx : L.getD j z0 = x) :
    PathAccepts h (rootOf h z0 L height) (honestSibs h z0 L j) height j x :=
  ⟨hj, by rw [← hx]; exact honest_walk_root h z0 L height j hj⟩

theorem stored_root_witness (K : Roles) (h : Hash) (hl : LeafHash) (a b : UInt256)
    (ha : 0 < a) (hab : a < b) :
    LevelRun hl (genesisRun a b) (genesisTx K a b) (genesisLevel hl a b)
      ∧ storedLeaves (genesisLevel hl a b 3) (genesisRun a b 3).leafCount
          = [hl ⟨0, 1, a⟩, hl ⟨a, 2, b⟩, hl ⟨b, 0, 0⟩]
      ∧ fmHeight (genesisRun a b 3).leafCount = 2
      ∧ InclusionAccepted h hl
          (rootOf h (hl ⟨0, 0, 0⟩) (storedLeaves (genesisLevel hl a b 3) 3) 2) a ⟨a, 2, b⟩ 1
          (honestSibs h (hl ⟨0, 0, 0⟩) (storedLeaves (genesisLevel hl a b 3) 3) 1) 2
      ∧ NonInclusionAccepted h hl
          (rootOf h (hl ⟨0, 0, 0⟩) (storedLeaves (genesisLevel hl a b 3) 3) 2) a ⟨0, 0, 0⟩ 3
          (honestSibs h (hl ⟨0, 0, 0⟩) (storedLeaves (genesisLevel hl a b 3) 3) 3) 2
      ∧ ¬ TreeRootBreak h (hl ⟨0, 0, 0⟩) hl (genesisRun a b 3) 2
          (honestSibs h (hl ⟨0, 0, 0⟩) (storedLeaves (genesisLevel hl a b 3) 3) 1) 2 1 ⟨a, 2, b⟩
      ∧ TreeRootBreak h (hl ⟨0, 0, 0⟩) hl (genesisRun a b 3) 2
          (honestSibs h (hl ⟨0, 0, 0⟩) (storedLeaves (genesisLevel hl a b 3) 3) 3) 2 3
          ⟨0, 0, 0⟩ := by
  obtain ⟨hg1, hg2⟩ := threeLeafTree_guards ha hab
  have hlev : LevelRun hl (genesisRun a b) (genesisTx K a b) (genesisLevel hl a b) := by
    intro n
    match n with
    | 0 => rfl
    | 1 =>
      show genesisLevel hl a b 2 = levelWrites hl setup (genesisLevel hl a b 1) (.insert a 0)
      rw [levelWrites_insert (insertChecks_of_guard hg1)]
      rfl
    | 2 =>
      show genesisLevel hl a b 3
        = levelWrites hl (insert setup a 0) (genesisLevel hl a b 2) (.insert b 1)
      rw [levelWrites_insert (insertChecks_of_guard hg2)]
      rfl
    | n + 3 => rfl
  have hst : storedLeaves (genesisLevel hl a b 3) 3
      = [hl ⟨0, 1, a⟩, hl ⟨a, 2, b⟩, hl ⟨b, 0, 0⟩] := rfl
  have hmodel : storedLeaves (genesisLevel hl a b 3) 3 = leafHashes hl (genesisRun a b 3) := rfl
  have hc3 : (genesisRun a b 3).leafCount = 3 := rfl
  have hnb := honest_proof_no_break h (hl ⟨0, 0, 0⟩) hl (genesisRun a b 3) 2 1
    (by rw [hc3]; omega)
  rw [← hmodel] at hnb
  refine ⟨hlev, hst, rfl, ⟨rfl, stored_path_accepts _ (by norm_num) (by rw [hst]; rfl)⟩,
    ⟨(ne_of_lt ha).symm, ha, Or.inl rfl,
      stored_path_accepts _ (by norm_num) (by rw [hst]; rfl)⟩, hnb,
    TreeRootBreak.paddingHit (by rw [hc3]) rfl⟩

theorem guardless_reinit_forges_absence_at_stored_root (K : Roles) (h : Hash) (z0 : UInt256)
    (hl : LeafHash) (a : UInt256) (ha : a ≠ 0) :
    LevelRun hl (reinitRun a) (reinitTx K a) (reinitLevel hl a)
      ∧ storedLeaves (reinitLevel hl a 3) (reinitRun a 3).leafCount
          = [hl ⟨0, 1, a⟩, hl ⟨a, 0, 0⟩, hl ⟨0, 0, 0⟩]
      ∧ leafHashes hl (reinitRun a 3) = [hl ⟨0, 0, 0⟩, hl ⟨a, 0, 0⟩, hl ⟨0, 0, 0⟩]
      ∧ fmHeight (reinitRun a 3).leafCount = 2
      ∧ InclusionAccepted h hl
          (rootOf h z0 (storedLeaves (reinitLevel hl a 3) 3) 2) a ⟨a, 0, 0⟩ 1
          (honestSibs h z0 (storedLeaves (reinitLevel hl a 3) 3) 1) 2
      ∧ NonInclusionAccepted h hl
          (rootOf h z0 (storedLeaves (reinitLevel hl a 3) 3) 2) a ⟨0, 0, 0⟩ 2
          (honestSibs h z0 (storedLeaves (reinitLevel hl a 3) 3) 2) 2 := by
  have hlev : LevelRun hl (reinitRun a) (reinitTx K a) (reinitLevel hl a) := by
    intro n
    match n with
    | 0 => rfl
    | 1 =>
      show reinitLevel hl a 2 = levelWrites hl setup (reinitLevel hl a 1) (.insert a 0)
      rw [levelWrites_insert (setup_insertChecks ha)]
      rfl
    | 2 => rfl
    | n + 3 => rfl
  have hst : storedLeaves (reinitLevel hl a 3) 3 = [hl ⟨0, 1, a⟩, hl ⟨a, 0, 0⟩, hl ⟨0, 0, 0⟩] :=
    rfl
  refine ⟨hlev, hst, rfl, rfl, ⟨rfl, stored_path_accepts _ (by norm_num) (by rw [hst]; rfl)⟩,
    ⟨ha, Fin.pos_iff_ne_zero.mpr ha, Or.inl rfl,
      stored_path_accepts _ (by norm_num) (by rw [hst]; rfl)⟩⟩

end LeafLevel

/-! ## Certificates -/

theorem InitL2OnPredeploy : Properties.InitL2OnPredeploy := initL2_on_predeploy
theorem InitL2RevertsOnceInitialized : Properties.InitL2RevertsOnceInitialized :=
  initL2_reverts_once_initialized
theorem InsertRevertsBeforeInit : Properties.InsertRevertsBeforeInit := insert_reverts_before_init
theorem TxStepCallerIsRole : Properties.TxStepCallerIsRole := txStep_caller_is_role
theorem InitL2AtMostOnce : Properties.InitL2AtMostOnce := initL2_at_most_once
theorem NoInitL2OnceInitialized : Properties.NoInitL2OnceInitialized :=
  noInitL2_once_initialized
theorem NoRunFromSetupReinitializes : Properties.NoRunFromSetupReinitializes :=
  noRun_from_setup_reinitializes
theorem TxRunAppendOnly : Properties.TxRunAppendOnly := txRun_appendOnly
theorem TxRunKeysMono : Properties.TxRunKeysMono := txRun_keysMono
theorem ResetHistoryUnreachable : Properties.ResetHistoryUnreachable := resetHistory_unreachable
theorem TxRunFromValidIsRun : Properties.TxRunFromValidIsRun := txRun_from_valid_is_run
theorem RunLiftsToTxRun : Properties.RunLiftsToTxRun := run_lifts_to_txRun
theorem PredeployRunShape : Properties.PredeployRunShape := predeploy_run_shape
theorem PredeployRunStates : Properties.PredeployRunStates := predeploy_run_states
theorem PredeployRunReclaimableIffAbsent : Properties.PredeployRunReclaimableIffAbsent :=
  predeploy_run_reclaimable_iff_absent
theorem GenesisRunWitness : Properties.GenesisRunWitness := genesisRun_witness
theorem GuardlessReinitBreaksExclusivity : Properties.GuardlessReinitBreaksExclusivity :=
  guardless_reinit_breaks_exclusivity
theorem GuardlessRunsKeepKeys : Properties.GuardlessRunsKeepKeys := guardless_runs_keep_keys
theorem GuardlessResetHistoryUnreachable : Properties.GuardlessResetHistoryUnreachable :=
  guardless_resetHistory_unreachable
theorem StoredLeavesAreLeafHashes : Properties.StoredLeavesAreLeafHashes :=
  stored_leaves_are_leafHashes
theorem PredeployStoredRootExclusiveOrBreak : Properties.PredeployStoredRootExclusiveOrBreak :=
  predeploy_stored_root_exclusive_or_break
theorem StoredRootWitness : Properties.StoredRootWitness := stored_root_witness
theorem GuardlessReinitForgesAbsenceAtStoredRoot :
    Properties.GuardlessReinitForgesAbsenceAtStoredRoot :=
  guardless_reinit_forges_absence_at_stored_root

end Contracts.InteropCommitmentTree
