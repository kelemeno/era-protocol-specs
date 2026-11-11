import EraSpec.Protocol.InteropAtomicity.Properties.OncePerLeg
import EraSpec.Protocol.InteropAtomicity.Proofs.Refund
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.HintSearch
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.Reaches
import EraSpec.Contracts.AtomicFlowManager.Proofs.Model

/-!
# Proofs: each leg is appended once and occupies one tree key

One invariant (`Inv`), proved by induction over a run from genesis, carries everything:
the tree is valid, its key set is the sentinel plus the logged commit values, those values
are pairwise distinct and nonzero, the `k`-th append sits at index `k + 1`, and the manager
has a leg `Unset` exactly when it is not logged.

The `append` case is where the three components meet.  The tree's insert flow gives
`InsertGuard` (`search_yields_guard`).  `insert_preserves_valid` and `insert_sound_step`
carry validity and the key set.  `dedup_gate_sound` shows the new commit value is not yet a
key, so it differs from every logged one.  The manager's `set` lemmas carry the `Unset`
characterization.  The other three steps never touch the tree, and `initL2` cannot fire
on a tree with a leaf.

`NoSecondAppend` is proved separately from the invariant, by projecting the continuation
onto the manager (`no_double_append`) and onto the tree (`ReachesKeysMono`, then
`dedup_gate_sound`).  `CommitmentPinsLoggedLeg` goes through
`Contracts.Refund.CommitmentPinsLegOn` with its premise discharged.
-/

namespace Contracts.AppendPath

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund

/-! ## Reading the composed state -/

@[simp] lemma appended_mgr (s : ChainState) (cv : CommitValue) (f b : UInt256) (low : ℕ) :
    (s.appended cv f b low).mgr = s.mgr.set f b .Committed := rfl

@[simp] lemma appended_tree (s : ChainState) (cv : CommitValue) (f b : UInt256) (low : ℕ) :
    (s.appended cv f b low).tree = Contracts.InteropCommitmentTree.insert s.tree (cv f b) low :=
  rfl

@[simp] lemma commitOf_mk (cv : CommitValue) (f b : UInt256) (c : Chain) :
    commitOf cv ⟨f, b, c⟩ = cv f b := rfl

/-- The contract's insert flow, on a valid tree, is the guarded insert. -/
lemma InsertSucceeds.guard {T : Tree} (hV : Valid T) {v : UInt256} {hint low : ℕ}
    (h : InsertSucceeds T v hint low) : InsertGuard T v low :=
  search_yields_guard hV h.initialized h.nonzero h.fresh h.hintInBounds h.hintBelow h.search

/-- A value the tree's insert accepts is not yet a key: `dedup_gate_sound`. -/
lemma InsertSucceeds.not_key {T : Tree} (hV : Valid T) {v : UInt256} {hint low : ℕ}
    (h : InsertSucceeds T v hint low) : v ∉ keys (toAbs T) :=
  dedup_gate_sound hV h.nonzero h.fresh

/-- Inserting changes no value except at the new index. -/
lemma insert_value_of_ne {T : Tree} {v : UInt256} {low i : ℕ} (hi : i ≠ T.leafCount) :
    ((Contracts.InteropCommitmentTree.insert T v low).leaf i).value = (T.leaf i).value := by
  by_cases hl : i = low
  · subst hl
    rw [insert_leaf_low]
  · rw [insert_leaf_other hl hi]

/-- In a valid tree, a nonzero key is registered in `valueToIndex`. -/
lemma registered_of_key {T : Tree} (hV : Valid T) {v : UInt256} (hv : v ≠ 0)
    (hk : v ∈ keys (toAbs T)) : T.valueToIndex v ≠ 0 := by
  intro h0
  exact dedup_gate_sound hV hv h0 hk

/-! ## The run invariant -/

/-- What every run from genesis keeps. -/
structure Inv (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation) : Prop where
  valid : Valid s.tree
  count : s.tree.leafCount = log.length + 1
  keysEq : keys (toAbs s.tree) = Insert.insert 0 (log.map (commitOf cv)).toFinset
  valsNodup : (log.map (commitOf cv)).Nodup
  valsNe : ∀ o ∈ log, commitOf cv o ≠ 0
  chainEq : ∀ o ∈ log, o.chain = c
  mgrUnset : ∀ f b, s.mgr.legState f b = .Unset ↔ (⟨f, b, c⟩ : Obligation) ∉ log
  positions : (List.range log.length).map (fun k => (s.tree.leaf (k + 1)).value)
    = log.reverse.map (commitOf cv)

lemma inv_genesis (cv : CommitValue) (c : Chain) : Inv cv c genesis [] where
  valid := setup_valid
  count := rfl
  keysEq := by
    show keys (toAbs setup) = _
    rw [toAbs_setup]
    simp [keys]
  valsNodup := List.nodup_nil
  valsNe := by simp
  chainEq := by simp
  mgrUnset := by
    intro f b
    simp [genesis, Contracts.AtomicFlowManager.empty]
  positions := by simp

/-- A logged obligation's commit value is a key. -/
lemma Inv.key_of_mem {cv : CommitValue} {c : Chain} {s : ChainState} {log : List Obligation}
    (hI : Inv cv c s log) {o : Obligation} (ho : o ∈ log) :
    commitOf cv o ∈ keys (toAbs s.tree) := by
  rw [hI.keysEq]
  exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_map_of_mem ho))

/-- A nonzero key is the commit value of a logged obligation. -/
lemma Inv.mem_of_key {cv : CommitValue} {c : Chain} {s : ChainState} {log : List Obligation}
    (hI : Inv cv c s log) {v : UInt256} (hv : v ≠ 0) (hk : v ∈ keys (toAbs s.tree)) :
    ∃ o ∈ log, commitOf cv o = v := by
  rw [hI.keysEq, Finset.mem_insert] at hk
  rcases hk with h0 | hmem
  · exact absurd h0 hv
  · exact List.mem_map.mp (List.mem_toFinset.mp hmem)

/-- Two logged obligations with one commit value are equal. -/
lemma Inv.inj {cv : CommitValue} {c : Chain} {s : ChainState} {log : List Obligation}
    (hI : Inv cv c s log) {o o' : Obligation} (ho : o ∈ log) (ho' : o' ∈ log)
    (heq : commitOf cv o = commitOf cv o') : o = o' :=
  List.inj_on_of_nodup_map hI.valsNodup ho ho' heq

lemma inv_append {cv : CommitValue} {c : Chain} {t : ChainState} {log : List Obligation}
    {f b : UInt256} {hint low : ℕ} (hI : Inv cv c t log) (h : AppendSucceeds cv t f b hint low) :
    Inv cv c (t.appended cv f b low) (⟨f, b, c⟩ :: log) := by
  have hV := hI.valid
  have hg : InsertGuard t.tree (cv f b) low := h.treeInsert.guard hV
  have hfreshKey : cv f b ∉ keys (toAbs t.tree) := h.treeInsert.not_key hV
  have hnotin : cv f b ∉ log.map (commitOf cv) := by
    intro hmem
    obtain ⟨o, ho, hov⟩ := List.mem_map.mp hmem
    exact hfreshKey (hov ▸ hI.key_of_mem ho)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact insert_preserves_valid hV hg
  · show (Contracts.InteropCommitmentTree.insert t.tree (cv f b) low).leafCount = _
    rw [insert_leafCount, hI.count]
    simp
  · show keys (toAbs (Contracts.InteropCommitmentTree.insert t.tree (cv f b) low)) = _
    rw [(insert_sound_step hV hg).2, hI.keysEq, List.map_cons, List.toFinset_cons, commitOf_mk,
      Finset.insert_comm]
  · rw [List.map_cons, List.nodup_cons]
    exact ⟨hnotin, hI.valsNodup⟩
  · intro o ho
    rcases List.mem_cons.mp ho with rfl | ho
    · exact h.treeInsert.nonzero
    · exact hI.valsNe o ho
  · intro o ho
    rcases List.mem_cons.mp ho with rfl | ho
    · rfl
    · exact hI.chainEq o ho
  · intro f' b'
    by_cases hk : f' = f ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := hk
      simp only [appended_mgr, set_same]
      simp
    · simp only [appended_mgr]
      rw [set_other hk, hI.mgrUnset f' b']
      constructor
      · intro hnot hmem
        rcases List.mem_cons.mp hmem with he | hmem
        · exact hk ⟨congrArg Obligation.flowId he, congrArg Obligation.bundleHash he⟩
        · exact hnot hmem
      · intro hnot hmem
        exact hnot (List.mem_cons_of_mem _ hmem)
  · have hlow : low < t.tree.leafCount := hg.inBounds
    show (List.range (log.length + 1)).map
        (fun k => ((Contracts.InteropCommitmentTree.insert t.tree (cv f b) low).leaf (k + 1)).value)
      = (⟨f, b, c⟩ :: log).reverse.map (commitOf cv)
    rw [List.range_succ, List.map_append, List.reverse_cons, List.map_append, ← hI.positions]
    congr 1
    · apply List.map_congr_left
      intro k hk
      have hk' : k < log.length := List.mem_range.mp hk
      exact insert_value_of_ne (by rw [hI.count]; omega)
    · simp only [List.map_cons, List.map_nil, commitOf_mk]
      have hidx : log.length + 1 = t.tree.leafCount := hI.count.symm
      rw [hidx, insert_leaf_new hlow]

lemma inv_authorize {cv : CommitValue} {c : Chain} {t : ChainState} {log : List Obligation}
    {f b : UInt256} (hI : Inv cv c t log) (hg : AuthorizeGuard t.mgr f b) :
    Inv cv c ⟨t.mgr.set f b .Revertable, t.tree⟩ log := by
  refine ⟨hI.valid, hI.count, hI.keysEq, hI.valsNodup, hI.valsNe, hI.chainEq, ?_, hI.positions⟩
  intro f' b'
  by_cases hk : f' = f ∧ b' = b
  · obtain ⟨rfl, rfl⟩ := hk
    have hold := hI.mgrUnset f' b'
    have hc : t.mgr.legState f' b' = .Committed := hg
    rw [hc] at hold
    simp only [set_same]
    constructor
    · intro h; cases h
    · intro hnot
      exact absurd (hold.mpr hnot) (by decide)
  · show (t.mgr.set f b .Revertable).legState f' b' = .Unset ↔ _
    rw [set_other hk]
    exact hI.mgrUnset f' b'

lemma inv_claim {cv : CommitValue} {c : Chain} {t : ChainState} {log : List Obligation}
    {f b : UInt256} (hI : Inv cv c t log) (hg : ClaimGuard t.mgr f b) :
    Inv cv c ⟨t.mgr.set f b .Reverted, t.tree⟩ log := by
  refine ⟨hI.valid, hI.count, hI.keysEq, hI.valsNodup, hI.valsNe, hI.chainEq, ?_, hI.positions⟩
  intro f' b'
  by_cases hk : f' = f ∧ b' = b
  · obtain ⟨rfl, rfl⟩ := hk
    have hold := hI.mgrUnset f' b'
    have hc : t.mgr.legState f' b' = .Revertable := hg
    rw [hc] at hold
    simp only [set_same]
    constructor
    · intro h; cases h
    · intro hnot
      exact absurd (hold.mpr hnot) (by decide)
  · show (t.mgr.set f b .Reverted).legState f' b' = .Unset ↔ _
    rw [set_other hk]
    exact hI.mgrUnset f' b'

/-- **THE INVARIANT HOLDS ALONG EVERY RUN FROM GENESIS.** -/
theorem inv_of_steps {cv : CommitValue} {c : Chain} {s : ChainState} {log : List Obligation}
    (h : Steps cv c genesis s log) : Inv cv c s log := by
  induction h with
  | refl => exact inv_genesis cv c
  | append _ ha ih => exact inv_append ih ha
  | authorize _ hg ih => exact inv_authorize ih hg
  | claim _ hg ih => exact inv_claim ih hg
  | initL2 _ h0 ih =>
    exfalso
    have := ih.count
    omega

/-! ## Segments and projections -/

/-- Runs compose; the logs concatenate, later appends first. -/
theorem steps_trans {cv : CommitValue} {c : Chain} {s t u : ChainState}
    {l₁ l₂ : List Obligation} (h₁ : Steps cv c s t l₁) (h₂ : Steps cv c t u l₂) :
    Steps cv c s u (l₂ ++ l₁) := by
  induction h₂ with
  | refl => exact h₁
  | append _ ha ih => exact Steps.append ih ha
  | authorize _ hg ih => exact Steps.authorize ih hg
  | claim _ hg ih => exact Steps.claim ih hg
  | initL2 _ h0 ih => exact Steps.initL2 ih h0

/-- The manager half of a run is a manager run. -/
theorem steps_mgr_reach {cv : CommitValue} {c : Chain} {s t : ChainState}
    {log : List Obligation} (h : Steps cv c s t log) :
    Contracts.AtomicFlowManager.Reach s.mgr t.mgr := by
  induction h with
  | refl => exact Contracts.AtomicFlowManager.Reach.refl
  | append _ ha ih =>
    exact Contracts.AtomicFlowManager.Reach.tail ih
      (Contracts.AtomicFlowManager.Step.append ha.legUnset)
  | authorize _ hg ih =>
    exact Contracts.AtomicFlowManager.Reach.tail ih (Contracts.AtomicFlowManager.Step.authorize hg)
  | claim _ hg ih =>
    exact Contracts.AtomicFlowManager.Reach.tail ih (Contracts.AtomicFlowManager.Step.claim hg)
  | initL2 _ _ ih => exact ih

/-- The tree half of a run from a valid tree is a tree run. -/
theorem steps_tree_reaches {cv : CommitValue} {c : Chain} {s t : ChainState}
    {log : List Obligation} (h : Steps cv c s t log) (hV : Valid s.tree) :
    Reaches s.tree t.tree := by
  induction h with
  | refl => exact Reaches.refl
  | append _ ha ih =>
    exact Reaches.tail ih (ha.treeInsert.guard (reaches_valid ih hV))
  | authorize _ _ ih => exact ih
  | claim _ _ ih => exact ih
  | initL2 _ h0 ih =>
    exfalso
    have := (reaches_valid ih hV).occupied
    omega

/-! ## Once per leg -/

/-- The run discharges `CommitValueInjOn` on its own log. -/
theorem run_refutes_logged_commit_clash {cv : CommitValue} {c : Chain} {s : ChainState}
    {log : List Obligation} (h : Steps cv c genesis s log) : CommitValueInjOn cv log := by
  have hI := inv_of_steps h
  rintro o ho o' ho' ⟨hne, heq⟩
  exact hne (by rw [hI.inj ho ho' heq])

/-- `CommitmentPinsLegOn` with `os := log`: its premise is the previous theorem.  The chain
comes from the log. -/
theorem commitment_pins_logged_leg {cv : CommitValue} {c : Chain} {s : ChainState}
    {log : List Obligation} (h : Steps cv c genesis s log) {o o' : Obligation}
    (ho : o ∈ log) (ho' : o' ∈ log) (heq : commitOf cv o = commitOf cv o') : o = o' := by
  have hI := inv_of_steps h
  obtain ⟨hf, hb⟩ := Contracts.Refund.CommitmentPinsLegOn cv log
    (run_refutes_logged_commit_clash h) o ho o' ho' heq
  have hc : o.chain = o'.chain := (hI.chainEq o ho).trans (hI.chainEq o' ho').symm
  cases o
  cases o'
  simp_all

/-- Each logged obligation sits at exactly the index `valueToIndex` names. -/
theorem one_index_per_logged_obligation {cv : CommitValue} {c : Chain} {s : ChainState}
    {log : List Obligation} (h : Steps cv c genesis s log) {o : Obligation} (ho : o ∈ log) :
    0 < s.tree.valueToIndex (commitOf cv o)
      ∧ s.tree.valueToIndex (commitOf cv o) < s.tree.leafCount
      ∧ ∀ i < s.tree.leafCount,
          ((s.tree.leaf i).value = commitOf cv o ↔ i = s.tree.valueToIndex (commitOf cv o)) := by
  have hI := inv_of_steps h
  have hV := hI.valid
  have hreg : s.tree.valueToIndex (commitOf cv o) ≠ 0 :=
    registered_of_key hV (hI.valsNe o ho) (hI.key_of_mem ho)
  obtain ⟨hlt, hval⟩ := hV.vtiSound _ hreg
  refine ⟨Nat.pos_of_ne_zero hreg, hlt, ?_⟩
  intro i hi
  constructor
  · intro hvi
    exact hV.idxInj i hi _ hlt (hvi.trans hval.symm)
  · rintro rfl
    exact hval

end Contracts.AppendPath

/-! ## Certificates: the shape of every run, and once per leg -/

namespace Contracts.AppendPath

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund

theorem RunTreeIsSentinelThenLog : Properties.RunTreeIsSentinelThenLog := by
  intro cv c s log h
  have hI := inv_of_steps h
  exact ⟨hI.count, hI.valid.sentinel, hI.positions⟩

theorem RunKeysAreLoggedCommitValues : Properties.RunKeysAreLoggedCommitValues :=
  fun _ _ _ _ h => (inv_of_steps h).keysEq

theorem RunManagerTracksLog : Properties.RunManagerTracksLog :=
  fun _ _ _ _ h => ⟨(inv_of_steps h).chainEq, (inv_of_steps h).mgrUnset⟩

theorem RunProjectsToManagerReach : Properties.RunProjectsToManagerReach :=
  fun _ _ _ _ _ h => steps_mgr_reach h

theorem RunProjectsToTreeReaches : Properties.RunProjectsToTreeReaches :=
  fun _ _ _ _ _ h hV => steps_tree_reaches h hV

theorem RunSnapshotsMeetWfShape : Properties.RunSnapshotsMeetWfShape := by
  intro cv c snap h0 hstep
  have hrun : ∀ n, ∃ l, Steps cv c genesis (snap n) l := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      obtain ⟨l, hl⟩ := ih
      obtain ⟨l', hl'⟩ := hstep n
      exact ⟨l' ++ l, steps_trans hl hl'⟩
  obtain ⟨l0, hl0⟩ := h0
  refine ⟨steps_tree_reaches hl0 setup_valid, fun n => ?_⟩
  obtain ⟨l, hl⟩ := hrun n
  obtain ⟨l', hl'⟩ := hstep n
  exact steps_tree_reaches hl' (inv_of_steps hl).valid

theorem AppendedAtMostOnce : Properties.AppendedAtMostOnce :=
  fun cv _ _ _ h => List.Nodup.of_map (commitOf cv) (inv_of_steps h).valsNodup

theorem RunRefutesLoggedCommitClash : Properties.RunRefutesLoggedCommitClash :=
  fun _ _ _ _ h => run_refutes_logged_commit_clash h

theorem CommitmentPinsLoggedLeg : Properties.CommitmentPinsLoggedLeg :=
  fun _ _ _ _ h _ ho _ ho' heq => commitment_pins_logged_leg h ho ho' heq

theorem OneIndexPerLoggedObligation : Properties.OneIndexPerLoggedObligation :=
  fun _ _ _ _ h _ ho => one_index_per_logged_obligation h ho

theorem KeyNamesOneLoggedObligation : Properties.KeyNamesOneLoggedObligation := by
  intro cv c s log h v hv hv0
  have hI := inv_of_steps h
  obtain ⟨o, ho, hov⟩ := hI.mem_of_key hv0 hv
  exact ⟨o, ⟨ho, hov⟩, fun o' ⟨ho', hov'⟩ => hI.inj ho' ho (hov'.trans hov.symm)⟩

theorem OncePerLeg : Properties.OncePerLeg := by
  intro cv c s log h
  have hI := inv_of_steps h
  refine ⟨AppendedAtMostOnce cv c s log h, ?_,
    fun o ho o' ho' heq => commitment_pins_logged_leg h ho ho' heq⟩
  intro o ho
  obtain ⟨_, hlt, hiff⟩ := one_index_per_logged_obligation h ho
  refine ⟨hI.chainEq o ho, s.tree.valueToIndex (commitOf cv o), ⟨hlt, (hiff _ hlt).mpr rfl⟩, ?_⟩
  rintro i ⟨hi, hval⟩
  exact (hiff i hi).mp hval

theorem NoSecondAppend : Properties.NoSecondAppend := by
  intro cv c s log f b hint low t log' hrun happ hseg
  refine ⟨?_, ?_⟩
  · -- the manager: `no_double_append` on the continuation's manager run
    have hreach : Contracts.AtomicFlowManager.Reach (s.mgr.set f b .Committed) t.mgr :=
      steps_mgr_reach hseg
    exact no_double_append happ.legUnset hreach
  · -- the tree: the value stays a key (`ReachesKeysMono`), so the dedup gate refuses it
    intro hint' low' hins
    have hV : Valid s.tree := (inv_of_steps hrun).valid
    have hg := happ.treeInsert.guard hV
    have hV₁ : Valid (s.appended cv f b low).tree := insert_preserves_valid hV hg
    have hkey₁ : cv f b ∈ keys (toAbs (s.appended cv f b low).tree) := by
      show cv f b ∈ keys (toAbs (Contracts.InteropCommitmentTree.insert s.tree (cv f b) low))
      rw [(insert_sound_step hV hg).2]
      exact Finset.mem_insert_self _ _
    have hR := steps_tree_reaches hseg hV₁
    have hkey : cv f b ∈ keys (toAbs t.tree) := reaches_keys_mono hR hV₁ hkey₁
    exact hins.not_key (reaches_valid hR hV₁) hkey

theorem RefundedLegWasAppendedOnce : Properties.RefundedLegWasAppendedOnce := by
  intro cv c s log h f b hrank
  have hI := inv_of_steps h
  have hmem : (⟨f, b, c⟩ : Obligation) ∈ log := by
    by_contra hnot
    have hunset := (hI.mgrUnset f b).mpr hnot
    rw [hunset] at hrank
    simp [rank] at hrank
  exact ⟨List.count_eq_one_of_mem (AppendedAtMostOnce cv c s log h) hmem, hI.key_of_mem hmem⟩

end Contracts.AppendPath

/-! ## What a key says, and when the two gates disagree -/

namespace Contracts.AppendPath

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund

/-- The search stops at once on a leaf whose window already straddles the value. -/
lemma lowSearch_stop {T : Tree} {v : UInt256} {i : ℕ}
    (h : ¬ ((T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v)) (fuel : ℕ) :
    lowSearch T v fuel i = some i := by
  cases fuel with
  | zero =>
    simp only [lowSearch]
    exact ite_eq_right h
  | succ n =>
    simp only [lowSearch]
    exact ite_eq_right h

theorem KeyPinsAppendedLegOrClash : Properties.KeyPinsAppendedLegOrClash := by
  intro cv c s log h f b hv0 hkey
  have hI := inv_of_steps h
  obtain ⟨o, ho, hov⟩ := hI.mem_of_key hv0 hkey
  refine ⟨?_, ?_⟩
  · by_cases hp : (f, b) = (o.flowId, o.bundleHash)
    · left
      obtain ⟨hf, hb⟩ := Prod.mk.inj hp
      have hc : o.chain = c := hI.chainEq o ho
      have heq : (⟨f, b, c⟩ : Obligation) = o := by
        cases o
        simp_all
      exact heq ▸ ho
    · right
      exact ⟨o, ho, hp, hov.symm⟩
  · rintro ⟨hmem, o', ho', hne, heq⟩
    exact hne (by rw [← hI.inj hmem ho' heq])

theorem TreeGateImpliesManagerGate : Properties.TreeGateImpliesManagerGate := by
  intro cv c s log h f b hint low hins
  have hI := inv_of_steps h
  show s.mgr.legState f b = .Unset
  rw [hI.mgrUnset]
  intro hmem
  exact hins.not_key hI.valid (hI.key_of_mem hmem)

theorem GatesDisagreeOnlyOnLoggedClash : Properties.GatesDisagreeOnlyOnLoggedClash := by
  intro cv c s log h f b hv0
  have hI := inv_of_steps h
  have hpin := KeyPinsAppendedLegOrClash cv c s log h f b hv0
  constructor
  · rintro ⟨hunset, hreg⟩
    have hkey : cv f b ∈ keys (toAbs s.tree) := registered_is_key hI.valid hreg
    rcases (hpin hkey).1 with hmem | hcl
    · exact absurd hmem ((hI.mgrUnset f b).mp hunset)
    · exact hcl
  · rintro ⟨o, ho, hcl⟩
    have hkey : cv f b ∈ keys (toAbs s.tree) := by
      rw [show cv f b = commitOf cv o from hcl.2]
      exact hI.key_of_mem ho
    refine ⟨?_, registered_of_key hI.valid hv0 hkey⟩
    show s.mgr.legState f b = .Unset
    rw [hI.mgrUnset]
    intro hmem
    exact (hpin hkey).2 ⟨hmem, o, ho, hcl⟩

theorem AppendEnabledIff : Properties.AppendEnabledIff := by
  intro cv c s log h f b
  have hI := inv_of_steps h
  have hV := hI.valid
  constructor
  · rintro ⟨hint, low, happ⟩
    exact ⟨happ.treeInsert.nonzero, happ.treeInsert.not_key hV⟩
  · rintro ⟨hv0, hfresh⟩
    -- the leaf whose window straddles `cv f b`: `gap_witness_exists`, from the sentinel
    have hbelow : ∃ X ∈ toAbs s.tree, X.key < cv f b := by
      refine ⟨⟨(s.tree.leaf 0).value, (s.tree.leaf 0).nextValue⟩,
        mem_toAbs.mpr ⟨0, hV.occupied, rfl, rfl⟩, ?_⟩
      show (s.tree.leaf 0).value < cv f b
      rw [hV.sentinel]
      exact Fin.pos_iff_ne_zero.mpr hv0
    obtain ⟨W, hW, hWlt, hWwin⟩ :=
      gap_witness_exists hV.absSound.2.2.1 hV.absSound.2.2.2 hbelow hfresh
    obtain ⟨i, hi, hival, hinext⟩ := mem_toAbs.mp hW
    refine ⟨i, i, ?_, ?_⟩
    · show s.mgr.legState f b = .Unset
      rw [hI.mgrUnset]
      intro hmem
      exact hfresh (hI.key_of_mem hmem)
    · refine ⟨hV.occupied.ne', hv0, ?_, hi, by rw [hival]; exact hWlt, ?_⟩
      · by_contra hreg
        exact hfresh (registered_is_key hV hreg)
      · apply lowSearch_stop
        rintro ⟨hne, hlt⟩
        rw [hinext] at hne hlt
        rcases hWwin with h0 | hgt
        · exact hne h0
        · exact absurd hlt (not_lt.mpr hgt.le)

theorem AppendBlockedOnlyByClash : Properties.AppendBlockedOnlyByClash := by
  intro cv c s log h f b hunset hv0
  have hI := inv_of_steps h
  rw [AppendEnabledIff cv c s log h f b]
  constructor
  · intro hblocked
    have hkey : cv f b ∈ keys (toAbs s.tree) := by
      by_contra hk
      exact hblocked ⟨hv0, hk⟩
    rcases (KeyPinsAppendedLegOrClash cv c s log h f b hv0 hkey).1 with hmem | hcl
    · exact absurd hmem ((hI.mgrUnset f b).mp hunset)
    · exact hcl
  · rintro ⟨o, ho, hcl⟩ ⟨_, hk⟩
    apply hk
    rw [show cv f b = commitOf cv o from hcl.2]
    exact hI.key_of_mem ho

end Contracts.AppendPath

/-! ## Every chain at once

Two projections.  The managers of a system run are a `Contracts.Refund.ReachLog` run, step
for step.  Chain `c`'s state is a `Steps` run of chain `c`, logging the obligations appended
on `c`: a step on another chain leaves both unchanged.  Everything else is the per-chain
results read through the second projection. -/

namespace Contracts.AppendPath

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund

@[simp] lemma update_self (X : Chains) (c : Chain) (s : ChainState) : X.update c s c = s := by
  simp [Chains.update]

lemma update_other (X : Chains) {c x : Chain} (s : ChainState) (h : x ≠ c) :
    X.update c s x = X x := by
  simp [Chains.update, h]

lemma mgrs_update (X : Chains) (c : Chain) (s : ChainState) :
    (X.update c s).mgrs = setAt X.mgrs c s.mgr := by
  funext x
  by_cases hx : x = c
  · subst hx
    simp [Chains.mgrs, setAt, Chains.update]
  · simp [Chains.mgrs, setAt, Chains.update, hx]

lemma mgrs_update_same (X : Chains) (c : Chain) (s : ChainState) (h : s.mgr = (X c).mgr) :
    (X.update c s).mgrs = X.mgrs := by
  funext x
  by_cases hx : x = c
  · subst hx
    simp [Chains.mgrs, Chains.update, h]
  · simp [Chains.mgrs, Chains.update, hx]

/-- The managers of a system run are a logged refund run. -/
theorem sysSteps_reachLog {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {X Y : Chains} {log : List Obligation} {alog : List AuthCall}
    (hr : SysSteps h z0 hl cv fh S X Y log alog) :
    ReachLog h z0 hl cv fh S X.mgrs Y.mgrs alog := by
  induction hr with
  | refl => exact ReachLog.refl
  | @append Y log alog c f b hint low _ ha ih =>
    rw [mgrs_update]
    exact ReachLog.append (c := c) (f := f) (b := b) ih ha.legUnset
  | @authorize Y log alog a _ hv hg ih =>
    rw [mgrs_update]
    exact ReachLog.authorize a ih hv hg
  | @claim Y log alog c f b _ hg ih =>
    rw [mgrs_update]
    exact ReachLog.claim (c := c) (f := f) (b := b) ih hg
  | @initL2 Y log alog c _ _ ih =>
    rw [mgrs_update_same Y c ⟨(Y c).mgr, reseed (Y c).tree⟩ rfl]
    exact ih

/-- Each chain of a system run is a chain run, logging what was appended on it. -/
theorem sysSteps_chain {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {Y : Chains} {log : List Obligation} {alog : List AuthCall}
    (hr : SysSteps h z0 hl cv fh S genesisAll Y log alog) :
    ∀ c, Steps cv c genesis (Y c) (log.filter (fun o => o.chain = c)) := by
  induction hr with
  | refl => exact fun _ => Steps.refl
  | @append Y log alog c' f b hint low _ ha ih =>
    intro c
    by_cases hc : c = c'
    · subst hc
      rw [update_self, List.filter_cons_of_pos (by simp)]
      exact Steps.append (ih c) ha
    · rw [update_other _ _ hc, List.filter_cons_of_neg (by simp [Ne.symm hc])]
      exact ih c
  | @authorize Y log alog a _ _ hg ih =>
    intro c
    by_cases hc : c = a.leg.chain
    · rw [hc, update_self]
      exact Steps.authorize (ih a.leg.chain) hg
    · rw [update_other _ _ hc]
      exact ih c
  | @claim Y log alog c' f b _ hg ih =>
    intro c
    by_cases hc : c = c'
    · subst hc
      rw [update_self]
      exact Steps.claim (ih c) hg
    · rw [update_other _ _ hc]
      exact ih c
  | @initL2 Y log alog c' _ h0 ih =>
    intro c
    by_cases hc : c = c'
    · subst hc
      rw [update_self]
      exact Steps.initL2 (ih c) h0
    · rw [update_other _ _ hc]
      exact ih c

/-- An obligation is in the filtered log of its own chain iff it is in the log. -/
lemma mem_filter_chain {log : List Obligation} {o : Obligation} {c : Chain} :
    o ∈ log.filter (fun o => o.chain = c) ↔ o ∈ log ∧ o.chain = c := by
  simp [List.mem_filter]

/-- The count of an obligation is its count on its own chain. -/
lemma count_filter_chain (log : List Obligation) (o : Obligation) :
    (log.filter (fun o' => o'.chain = o.chain)).count o = log.count o :=
  List.count_filter (by simp)

/-- Every logged authorization marked an appended obligation. -/
theorem sys_authorized_appended {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {Y : Chains} {log : List Obligation} {alog : List AuthCall}
    (hr : SysSteps h z0 hl cv fh S genesisAll Y log alog) :
    ∀ a ∈ alog, obligationOf a.flow a.leg ∈ log := by
  induction hr with
  | refl => intro a ha; cases ha
  | append _ _ ih => intro a ha; exact List.mem_cons_of_mem _ (ih a ha)
  | @authorize Y log alog a hprev _ hg ih =>
    intro a' ha'
    rcases List.mem_cons.mp ha' with rfl | ha'
    · have hI := inv_of_steps (sysSteps_chain hprev a'.leg.chain)
      have hc : (Y a'.leg.chain).mgr.legState a'.flow.flowId a'.leg.bundleHash = .Committed := hg
      have hnot : ¬ (Y a'.leg.chain).mgr.legState a'.flow.flowId a'.leg.bundleHash = .Unset := by
        rw [hc]; decide
      have hmem := not_not.mp (mt (hI.mgrUnset _ _).mpr hnot)
      exact (mem_filter_chain.mp hmem).1
    · exact ih a' ha'
  | claim _ _ ih => exact ih
  | initL2 _ _ ih => exact ih

end Contracts.AppendPath

namespace Contracts.AppendPath

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund

theorem SystemProjectsToChainRuns : Properties.SystemProjectsToChainRuns :=
  fun _ _ _ _ _ _ _ _ _ hr => sysSteps_chain hr

theorem SystemProjectsToReachLog : Properties.SystemProjectsToReachLog :=
  fun _ _ _ _ _ _ _ _ _ _ hr => sysSteps_reachLog hr

theorem SystemOncePerLeg : Properties.SystemOncePerLeg := by
  intro h z0 hl cv fh S Y log alog hr
  have hc := sysSteps_chain hr
  have hown : ∀ {o : Obligation}, o ∈ log → o ∈ log.filter (fun o' => o'.chain = o.chain) :=
    fun ho => mem_filter_chain.mpr ⟨ho, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [List.nodup_iff_count_le_one]
    intro o
    rw [← count_filter_chain log o]
    exact List.nodup_iff_count_le_one.mp (AppendedAtMostOnce cv _ _ _ (hc o.chain)) o
  · intro o ho
    exact ((OncePerLeg cv _ _ _ (hc o.chain)).2.1 o (hown ho)).2
  · intro o ho o' ho' hch heq
    have ho'' : o' ∈ log.filter (fun x => x.chain = o.chain) := mem_filter_chain.mpr ⟨ho', hch.symm⟩
    exact commitment_pins_logged_leg (hc o.chain) (hown ho) ho'' heq

theorem SystemRefundedWasAppendedOnce : Properties.SystemRefundedWasAppendedOnce := by
  intro h z0 hl cv fh S Y log alog hr o hrf
  obtain ⟨hcount, hkey⟩ := RefundedLegWasAppendedOnce cv o.chain (Y o.chain) _
    (sysSteps_chain hr o.chain) o.flowId o.bundleHash hrf
  refine ⟨?_, hkey⟩
  rw [← count_filter_chain log o]
  exact hcount

theorem SystemAuthorizedWereAppended : Properties.SystemAuthorizedWereAppended := by
  intro h z0 hl cv fh S Y log alog hr
  refine ⟨sys_authorized_appended hr, ?_⟩
  intro a ha a' ha' hch hcl
  have hf : obligationOf a.flow a.leg ∈ log.filter (fun o => o.chain = a.leg.chain) :=
    mem_filter_chain.mpr ⟨sys_authorized_appended hr a ha, rfl⟩
  have hf' : obligationOf a'.flow a'.leg ∈ log.filter (fun o => o.chain = a.leg.chain) :=
    mem_filter_chain.mpr ⟨sys_authorized_appended hr a' ha', hch.symm⟩
  exact run_refutes_logged_commit_clash (sysSteps_chain hr a.leg.chain) _ hf _ hf' hcl

theorem SystemKeyPinsAppendedLegOrClash : Properties.SystemKeyPinsAppendedLegOrClash := by
  intro h z0 hl cv fh S Y log alog hr c f b hv0 hkey
  obtain ⟨h1, h2⟩ := KeyPinsAppendedLegOrClash cv c (Y c) _ (sysSteps_chain hr c) f b hv0 hkey
  refine ⟨?_, ?_⟩
  · rcases h1 with hm | ⟨o, ho, hcl⟩
    · exact Or.inl (mem_filter_chain.mp hm).1
    · exact Or.inr ⟨o, (mem_filter_chain.mp ho).1, (mem_filter_chain.mp ho).2, hcl⟩
  · rintro ⟨hm, o, ho, hoc, hcl⟩
    exact h2 ⟨mem_filter_chain.mpr ⟨hm, rfl⟩, o, mem_filter_chain.mpr ⟨ho, hoc⟩, hcl⟩

theorem SystemExecutedObligationNeverRefundedOrBreak :
    Properties.SystemExecutedObligationNeverRefundedOrBreak := by
  intro h z0 hl cv fh S hS F ev leg hex Y log alog hr
  exact Contracts.Refund.ExecutedObligationNeverRefundedOrBreak h z0 hl cv fh S hS F ev leg hex
    Y.mgrs alog (sysSteps_reachLog hr)

end Contracts.AppendPath

/-! ## Anti-vacuity and countermodels -/

namespace Contracts.AppendPath

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund

/-- Each leg's commit value is its bundle hash: honest on legs with distinct bundle
hashes. -/
def bundleCv : CommitValue := fun _ b => b

/-- Every leg's commit value is `1`: any two keys collide. -/
def constCv : CommitValue := fun _ _ => 1

/-- `append(0, 1, _, 0)` succeeds at genesis whenever the commit value of `(0, 1)` is `1`,
the search not hopping. -/
lemma append_01_genesis {cv : CommitValue} (h1 : cv 0 1 = 1) :
    AppendSucceeds cv genesis 0 1 0 0 := by
  refine ⟨rfl, ?_⟩
  rw [h1]
  exact ⟨by unfold Initialized; decide, by decide, rfl, by decide, by decide, by decide⟩

/-- The state after `append(0, 1, _, 0)`, for both commit values below. -/
lemma steps_01 {cv : CommitValue} (h1 : cv 0 1 = 1) :
    Steps cv 0 genesis (genesis.appended cv 0 1 0) [⟨0, 1, 0⟩] :=
  Steps.append (f := 0) (b := 1) (hint := 0) (low := 0) Steps.refl (append_01_genesis h1)

/-- The honest continuation from there: append `(0, 2)` from hint `0` (the search hops
once, to index `1`), authorize `(0, 1)`, claim `(0, 1)`. -/
lemma honest_continuation :
    Steps bundleCv 0 (genesis.appended bundleCv 0 1 0)
      ⟨(((genesis.appended bundleCv 0 1 0).appended bundleCv 0 2 1).mgr.set 0 1 .Revertable).set
          0 1 .Reverted,
        ((genesis.appended bundleCv 0 1 0).appended bundleCv 0 2 1).tree⟩
      [⟨0, 2, 0⟩] := by
  have h2 : AppendSucceeds bundleCv (genesis.appended bundleCv 0 1 0) 0 2 0 1 :=
    ⟨by unfold AppendGuard; decide, by unfold Initialized; decide, by decide, by decide,
      by decide, by decide, by decide⟩
  have r2 := Steps.append (c := 0) (f := 0) (b := 2) (hint := 0) (low := 1) Steps.refl h2
  have r3 := Steps.authorize (f := 0) (b := 1) r2 (by unfold AuthorizeGuard; decide)
  exact Steps.claim (f := 0) (b := 1) r3 (by unfold ClaimGuard; decide)

theorem OncePerLegWitness : Properties.OncePerLegWitness := by
  refine ⟨bundleCv, _, _, steps_trans (steps_01 rfl) honest_continuation, rfl, by decide,
    by decide, ?_⟩
  exact ⟨by unfold Initialized; decide, by decide, by decide, by decide, by decide, by decide⟩

theorem NoSecondAppendWitness : Properties.NoSecondAppendWitness :=
  ⟨bundleCv, genesis, [], 0, 1, 0, 0, _, _, Steps.refl, append_01_genesis rfl,
    honest_continuation, List.cons_ne_nil _ _⟩

/-- Genesis, then the state after the first append, then the end state of
`honest_continuation` from batch 2 on. -/
def witnessSnap : ℕ → ChainState
  | 0 => genesis
  | 1 => genesis.appended bundleCv 0 1 0
  | _ + 2 =>
    ⟨(((genesis.appended bundleCv 0 1 0).appended bundleCv 0 2 1).mgr.set 0 1 .Revertable).set
        0 1 .Reverted,
      ((genesis.appended bundleCv 0 1 0).appended bundleCv 0 2 1).tree⟩

theorem RunSnapshotsWitness : Properties.RunSnapshotsWitness := by
  refine ⟨bundleCv, witnessSnap, ⟨[], Steps.refl⟩, ?_, by decide, by decide⟩
  intro n
  match n with
  | 0 => exact ⟨_, steps_01 rfl⟩
  | 1 => exact ⟨_, honest_continuation⟩
  | _ + 2 => exact ⟨[], Steps.refl⟩

theorem HonestKeyHasNoClash : Properties.HonestKeyHasNoClash := by
  have r := steps_01 (cv := bundleCv) rfl
  refine ⟨bundleCv, _, _, 0, 1, r, by decide, (inv_of_steps r).key_of_mem
    (List.mem_singleton_self _), List.mem_singleton_self _, ?_, ?_⟩
  · rintro ⟨o, ho, hne, _⟩
    rw [List.mem_singleton] at ho
    subst ho
    exact hne rfl
  · rintro ⟨hunset, _⟩
    exact absurd hunset (by unfold AppendGuard; decide)

theorem ClashBlocksFreshLeg : Properties.ClashBlocksFreshLeg := by
  have r := steps_01 (cv := constCv) rfl
  have hreg : (genesis.appended constCv 0 1 0).tree.valueToIndex (constCv 0 2) ≠ 0 := by decide
  have hcl : CommitClash constCv ⟨0, 2, 0⟩ ⟨0, 1, 0⟩ := ⟨by decide, rfl⟩
  refine ⟨constCv, _, _, 0, 2, r, by decide, (inv_of_steps r).key_of_mem
    (List.mem_singleton_self (⟨0, 1, 0⟩ : Obligation)), by decide,
    ⟨⟨0, 1, 0⟩, List.mem_singleton_self _, hcl⟩, by unfold AppendGuard; decide, hreg, ?_,
    run_refutes_logged_commit_clash r, ?_⟩
  · rintro ⟨hint, low, happ⟩
    exact hreg happ.treeInsert.fresh
  · intro hinj
    exact hinj ⟨0, 2, 0⟩ List.mem_cons_self ⟨0, 1, 0⟩
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) hcl

theorem WithoutDedupClashOccupiesTwoIndices : Properties.WithoutDedupClashOccupiesTwoIndices := by
  have r := steps_01 (cv := constCv) rfl
  have hreg : (genesis.appended constCv 0 1 0).tree.valueToIndex (constCv 0 2) ≠ 0 := by decide
  refine ⟨constCv, _, _, 0, 2, 0, 0, r, ⟨⟨0, 1, 0⟩, List.mem_singleton_self _, by decide, rfl⟩,
    by unfold AppendGuard; decide,
    ⟨by unfold Initialized; decide, by decide, by decide, by decide, by decide⟩,
    fun hins => hreg hins.fresh, ?_⟩
  rintro ⟨i, ⟨_, _⟩, huniq⟩
  have h1 := huniq 1 ⟨by decide, by decide⟩
  have h2 := huniq 2 ⟨by decide, by decide⟩
  omega

/-! ### A system run on two chains -/

/-- After appending `⟨0, 1, 0⟩` (the leg of `subsetFlow 0 1`) on chain `0`. -/
def sysY1 : Chains := genesisAll.update 0 (genesis.appended constCv 0 1 0)

/-- Then `⟨1, 2, 1⟩` (leg `⟨1, 2⟩` of `mixedFlow 1 1 2`) on chain `1`. -/
def sysY2 : Chains := sysY1.update 1 (genesis.appended constCv 1 2 0)

lemma sysY1_one : sysY1 1 = genesis := update_other _ _ (by decide)

lemma sys_r1 (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    SysSteps h z0 hl constCv lengthFlowHash (mixedSystem 1) genesisAll sysY1 [⟨0, 1, 0⟩] [] :=
  SysSteps.append (c := 0) (f := 0) (b := 1) (hint := 0) (low := 0) SysSteps.refl
    (append_01_genesis rfl)

lemma sys_r2 (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    SysSteps h z0 hl constCv lengthFlowHash (mixedSystem 1) genesisAll sysY2
      [⟨1, 2, 1⟩, ⟨0, 1, 0⟩] [] := by
  have happ : AppendSucceeds constCv (sysY1 1) 1 2 0 0 := by
    rw [sysY1_one]
    exact ⟨rfl, by unfold Initialized; decide, by decide, rfl, by decide, by decide, by decide⟩
  have r := SysSteps.append (c := 1) (f := 1) (b := 2) (hint := 0) (low := 0) (sys_r1 h z0 hl)
    happ
  rw [sysY1_one] at r
  exact r

theorem SystemWitness : Properties.SystemWitness := by
  intro h z0 hl
  have h1 : (0 : UInt256) < 1 := by decide
  -- the timeout that authorizes leg `⟨1, 2⟩` of `mixedFlow 1 1 2`
  obtain ⟨N, p, href⟩ := (subset_flow_passes_unchecked_gate (h := h) (z0 := z0) (hl := hl)
    (cv := constCv) (id := 1) (hA := 1) (hB := 2) h1 h1).2.2
  have hmem : (⟨1, 2⟩ : FlowLeg) ∈ (mixedFlow 1 1 2).legs := by simp [mixedFlow]
  have hv : AuthCall.Verified h z0 hl constCv lengthFlowHash (mixedSystem 1)
      ⟨mixedFlow 1 1 2, ⟨1, 2⟩, ⟨1, 2⟩, N, p⟩ :=
    ⟨lengthFlowHash_checks_mixed, hmem, hmem, href⟩
  have hg : AuthorizeGuard (sysY2 1).mgr 1 2 := by
    rw [show sysY2 1 = genesis.appended constCv 1 2 0 from update_self _ _ _]
    unfold AuthorizeGuard
    decide
  have r3 := SysSteps.authorize ⟨mixedFlow 1 1 2, ⟨1, 2⟩, ⟨1, 2⟩, N, p⟩ (sys_r2 h z0 hl) hv hg
  refine ⟨constCv, lengthFlowHash, mixedSystem 1, subsetFlow 0 1,
    fun _ => (0, honestProof h z0 hl (mixedSystem 1) 0 0 1), ⟨0, 1⟩, _, _, _,
    mixedSystem_wf h1, (subsetFlow_executes h z0 hl lengthFlowHash lengthFlowHash_checks_subset).1,
    r3, by simp [obligationOf, subsetFlow], List.cons_ne_nil _ _, ⟨⟨1, 2, 1⟩, ?_⟩, ?_, ?_,
    ⟨0, 1, 0⟩, by simp, ⟨1, 2, 1⟩, by simp, by decide, rfl⟩
  · -- the authorized leg is past `Committed`
    show 2 ≤ rank ((sysY2.update 1 ⟨(sysY2 1).mgr.set 1 2 .Revertable, (sysY2 1).tree⟩ 1).mgr.legState
      1 2)
    rw [update_self]
    simp [Manager.set, rank]
  · -- no logged call marked the executed obligation
    have hneq : obligationOf (mixedFlow 1 1 2) ⟨1, 2⟩ ≠ obligationOf (subsetFlow 0 1) ⟨0, 1⟩ := by
      intro he
      have hid : (1 : UInt256) = 0 := congrArg Obligation.flowId he
      exact absurd hid (by decide)
    intro hb
    cases hb with
    | flowIdClash a ha hobl _ =>
      rw [List.mem_singleton] at ha; subst ha; exact hneq hobl
    | inclusion a ha hobl _ _ =>
      rw [List.mem_singleton] at ha; subst ha; exact hneq hobl
    | absence a ha hobl _ _ =>
      rw [List.mem_singleton] at ha; subst ha; exact hneq hobl
  · -- the executed obligation is still `Committed` on chain `0`
    show ¬ 2 ≤ rank ((sysY2.update 1 ⟨(sysY2 1).mgr.set 1 2 .Revertable, (sysY2 1).tree⟩ 0).mgr.legState
      0 1)
    rw [update_other _ _ (by decide : (0 : Chain) ≠ 1),
      show sysY2 0 = sysY1 0 from update_other _ _ (by decide : (0 : Chain) ≠ 1),
      show sysY1 0 = genesis.appended constCv 0 1 0 from update_self _ _ _]
    simp [Manager.set, rank]

end Contracts.AppendPath
