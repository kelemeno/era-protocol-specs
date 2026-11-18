import EraSpec.Contracts.InteropRootStorage.Properties.Storage

/-!
# Proofs: `L2InteropRootStorage`

Every run-level result reduces to one fact about a single `_addInteropRoot`
(`addInteropRoot_iff`): it succeeds only on a key whose root slot is zero, and writes a nonzero
root there.  A successful external call is the bootloader's and is a sequence of such imports
(`exec_eq_some`), so a logged run from `S₀` is `addRoots S₀ (imports log)` (`reachLog_addRoots`)
and the log-level results are inductions on that list.  Relations that are reflexive,
transitive and hold of one import hold of every run (`reach_of_addRoot_rel`).
-/

namespace Contracts.InteropRootStorage

/-! ### One import -/

theorem addInteropRoot_iff {S S' : State} {chainId blockOrBatchNumber timestamp : UInt256}
    {sides : List UInt256} :
    addInteropRoot S chainId blockOrBatchNumber timestamp sides = some S' ↔
      ∃ root, sides = [root] ∧ root ≠ 0 ∧ timestamp ≠ 0 ∧
        (S.storedInteropRoots chainId blockOrBatchNumber).root = 0 ∧
        S' = writeRoot S chainId blockOrBatchNumber timestamp root := by
  unfold addInteropRoot
  constructor
  · intro h
    split_ifs at h with h1 h2 h3 h4
    obtain ⟨root, rfl⟩ := List.length_eq_one_iff.mp (not_not.mp h1)
    exact ⟨root, rfl, h2, h3, not_not.mp h4, (Option.some.inj h).symm⟩
  · rintro ⟨root, rfl, hr, ht, hs, rfl⟩
    simp [hr, ht, hs]

lemma addRoot_iff {S S' : State} {r : InteropRoot} :
    addRoot S r = some S' ↔
      ∃ root, r.sides = [root] ∧ root ≠ 0 ∧ r.timestamp ≠ 0 ∧
        (S.storedInteropRoots r.chainId r.blockOrBatchNumber).root = 0 ∧
        S' = writeRoot S r.chainId r.blockOrBatchNumber r.timestamp root :=
  addInteropRoot_iff

/-- A well-formed import at an unset key succeeds. -/
lemma addRoot_mk {S : State} {c b ts root : UInt256} (hr : root ≠ 0) (ht : ts ≠ 0)
    (hs : (S.storedInteropRoots c b).root = 0) :
    addRoot S ⟨c, b, ts, [root]⟩ = some (writeRoot S c b ts root) :=
  addRoot_iff.mpr ⟨root, rfl, hr, ht, hs, rfl⟩

/-! ### The written state, field by field -/

lemma writeRoot_stored_self (S : State) (c b ts root : UInt256) :
    (writeRoot S c b ts root).storedInteropRoots c b = ⟨root, ts⟩ := by
  simp [writeRoot]

lemma writeRoot_stored_ne (S : State) {c b c' b' : UInt256} (ts root : UInt256)
    (h : (c', b') ≠ (c, b)) :
    (writeRoot S c b ts root).storedInteropRoots c' b' = S.storedInteropRoots c' b' := by
  simp only [writeRoot]
  rw [if_neg]
  rintro ⟨rfl, rfl⟩
  exact h rfl

lemma writeRoot_latest_self (S : State) (c b ts root : UInt256) :
    (writeRoot S c b ts root).latestInteropRootTimestamp c
      = max (S.latestInteropRootTimestamp c) ts := by
  simp only [writeRoot, true_and]
  split_ifs with h
  · exact (max_eq_right h.le).symm
  · exact (max_eq_left (not_lt.mp h)).symm

lemma writeRoot_latest_ne (S : State) {c c' : UInt256} (b ts root : UInt256) (h : c' ≠ c) :
    (writeRoot S c b ts root).latestInteropRootTimestamp c' = S.latestInteropRootTimestamp c' := by
  simp [writeRoot, h]

lemma le_writeRoot_latest (S : State) (c b ts root c' : UInt256) :
    S.latestInteropRootTimestamp c' ≤ (writeRoot S c b ts root).latestInteropRootTimestamp c' := by
  by_cases h : c' = c
  · subst h
    rw [writeRoot_latest_self]
    exact le_max_left _ _
  · rw [writeRoot_latest_ne S b ts root h]

theorem add_interop_root_effect {S S' : State} {chainId blockOrBatchNumber timestamp root : UInt256}
    (h : addInteropRoot S chainId blockOrBatchNumber timestamp [root] = some S') :
    S'.storedInteropRoots chainId blockOrBatchNumber = ⟨root, timestamp⟩ ∧
    (∀ c b, (c, b) ≠ (chainId, blockOrBatchNumber) →
      S'.storedInteropRoots c b = S.storedInteropRoots c b) ∧
    S'.latestInteropRootTimestamp chainId = max (S.latestInteropRootTimestamp chainId) timestamp ∧
    (∀ c, c ≠ chainId → S'.latestInteropRootTimestamp c = S.latestInteropRootTimestamp c) := by
  obtain ⟨root', hsides, -, -, -, rfl⟩ := addInteropRoot_iff.mp h
  obtain rfl : root = root' := by simpa using hsides
  exact ⟨writeRoot_stored_self .., fun c b hne => writeRoot_stored_ne S _ _ hne,
    writeRoot_latest_self .., fun c hne => writeRoot_latest_ne S _ _ _ hne⟩

/-! ### Calls are bootloader batches of imports -/

lemma addRoots_singleton (S : State) (r : InteropRoot) : addRoots S [r] = addRoot S r := by
  simp only [addRoots]
  cases addRoot S r <;> rfl

lemma addRoots_cons_eq_some {S S' : State} {r : InteropRoot} {rs : List InteropRoot} :
    addRoots S (r :: rs) = some S' ↔ ∃ S₁, addRoot S r = some S₁ ∧ addRoots S₁ rs = some S' := by
  simp only [addRoots]
  cases h : addRoot S r with
  | none => simp
  | some S₁ => simp

lemma addRoots_append_eq_some {S S' : State} {xs ys : List InteropRoot} :
    addRoots S (xs ++ ys) = some S' ↔ ∃ S₁, addRoots S xs = some S₁ ∧ addRoots S₁ ys = some S' := by
  induction xs generalizing S with
  | nil => simp [addRoots]
  | cons x xs ih =>
    rw [List.cons_append, addRoots_cons_eq_some]
    constructor
    · rintro ⟨S₁, h1, h2⟩
      obtain ⟨S₂, h3, h4⟩ := ih.mp h2
      exact ⟨S₂, addRoots_cons_eq_some.mpr ⟨S₁, h1, h3⟩, h4⟩
    · rintro ⟨S₂, h3, h4⟩
      obtain ⟨S₁, h1, h2⟩ := addRoots_cons_eq_some.mp h3
      exact ⟨S₁, h1, ih.mpr ⟨S₂, h2, h4⟩⟩

/-- A successful call is the bootloader's, and is the sequence of its imports. -/
lemma exec_eq_some {S S' : State} {caller : Address} {c : Call} :
    exec S caller c = some S' ↔ caller = L2_BOOTLOADER_ADDRESS ∧ addRoots S c.roots = some S' := by
  cases c with
  | single r =>
    simp only [exec, addSingleInteropRoot, Call.roots, addRoots_singleton]
    by_cases hc : caller = L2_BOOTLOADER_ADDRESS <;> simp [hc]
  | batch rs =>
    simp only [exec, addInteropRootsInBatch, Call.roots]
    by_cases hc : caller = L2_BOOTLOADER_ADDRESS <;> simp [hc]

theorem only_bootloader_writes {S S' : State} {caller : Address} {c : Call}
    (h : exec S caller c = some S') : caller = L2_BOOTLOADER_ADDRESS :=
  (exec_eq_some.mp h).1

lemma imports_snoc (log : List (Address × Call)) (p : Address × Call) :
    imports (log ++ [p]) = imports log ++ p.2.roots := by
  simp [imports]

/-- A logged run is the sequence of its imports. -/
lemma reachLog_addRoots {S₀ S : State} {log : List (Address × Call)} (h : ReachLog S₀ S log) :
    addRoots S₀ (imports log) = some S := by
  induction h with
  | refl => rfl
  | tail caller c _ hexec ih =>
    rw [imports_snoc]
    exact addRoots_append_eq_some.mpr ⟨_, ih, (exec_eq_some.mp hexec).2⟩

theorem reach_iff_reachLog {S T : State} : Reach S T ↔ ∃ log, ReachLog S T log := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], ReachLog.refl⟩
    | tail _ hstep ih =>
      obtain ⟨log, hlog⟩ := ih
      obtain ⟨caller, c, hexec⟩ := hstep
      exact ⟨_, ReachLog.tail caller c hlog hexec⟩
  · rintro ⟨log, h⟩
    induction h with
    | refl => exact Reach.refl
    | tail caller c _ hexec ih => exact Reach.tail ih (Step.call caller c hexec)

theorem logged_callers_are_bootloader {S₀ S : State} {log : List (Address × Call)}
    (h : ReachLog S₀ S log) : ∀ p ∈ log, p.1 = L2_BOOTLOADER_ADDRESS := by
  induction h with
  | refl => intro p hp; simp at hp
  | tail caller c _ hexec ih =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ih p hp
    · obtain rfl : p = (caller, c) := by simpa using hp
      exact only_bootloader_writes hexec

lemma reach_trans {S T U : State} (h1 : Reach S T) (h2 : Reach T U) : Reach S U := by
  induction h2 with
  | refl => exact h1
  | tail _ hstep ih => exact Reach.tail ih hstep

/-- One import by the bootloader is a step. -/
lemma reach_of_addRoot {S S' : State} {r : InteropRoot} (h : addRoot S r = some S') : Reach S S' :=
  Reach.tail Reach.refl (Step.call L2_BOOTLOADER_ADDRESS (.single r) (by
    simpa [exec, addSingleInteropRoot] using h))

lemma reach_of_addRoots {S S' : State} {rs : List InteropRoot} (h : addRoots S rs = some S') :
    Reach S S' := by
  induction rs generalizing S with
  | nil =>
    obtain rfl : S = S' := by simpa [addRoots] using h
    exact Reach.refl
  | cons r rs ih =>
    obtain ⟨S₁, h1, h2⟩ := addRoots_cons_eq_some.mp h
    exact reach_trans (reach_of_addRoot h1) (ih h2)

/-- A relation that is reflexive, transitive and holds of one successful import holds of every
sequence of imports. -/
lemma addRoots_rel (Q : State → State → Prop) (hrefl : ∀ S, Q S S)
    (htrans : ∀ S T U, Q S T → Q T U → Q S U)
    (hadd : ∀ S r S', addRoot S r = some S' → Q S S') :
    ∀ (rs : List InteropRoot) (S S' : State), addRoots S rs = some S' → Q S S' := by
  intro rs
  induction rs with
  | nil =>
    intro S S' h
    obtain rfl : S = S' := by simpa [addRoots] using h
    exact hrefl S
  | cons r rs ih =>
    intro S S' h
    obtain ⟨S₁, h1, h2⟩ := addRoots_cons_eq_some.mp h
    exact htrans _ _ _ (hadd _ _ _ h1) (ih _ _ h2)

/-- … and of every run. -/
lemma reach_of_addRoot_rel (Q : State → State → Prop) (hrefl : ∀ S, Q S S)
    (htrans : ∀ S T U, Q S T → Q T U → Q S U)
    (hadd : ∀ S r S', addRoot S r = some S' → Q S S') :
    ∀ (S S' : State), Reach S S' → Q S S' := by
  intro S S' h
  induction h with
  | refl => exact hrefl _
  | tail _ hstep ih =>
    obtain ⟨caller, c, hexec⟩ := hstep
    exact htrans _ _ _ ih (addRoots_rel Q hrefl htrans hadd _ _ _ (exec_eq_some.mp hexec).2)

/-! ### No overwrite -/

lemma addRoot_no_overwrite {S S' : State} {r : InteropRoot} (h : addRoot S r = some S')
    {c b : UInt256} (hset : (S.storedInteropRoots c b).root ≠ 0) :
    S'.storedInteropRoots c b = S.storedInteropRoots c b := by
  obtain ⟨root, -, -, -, hunset, rfl⟩ := addRoot_iff.mp h
  refine writeRoot_stored_ne S _ _ ?_
  rintro heq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  exact hset hunset

theorem no_overwrite {S S' : State} (h : Reach S S') {c b : UInt256}
    (hset : (S.storedInteropRoots c b).root ≠ 0) :
    S'.storedInteropRoots c b = S.storedInteropRoots c b := by
  refine reach_of_addRoot_rel
    (fun S S' => ∀ c b, (S.storedInteropRoots c b).root ≠ 0 →
      S'.storedInteropRoots c b = S.storedInteropRoots c b)
    (fun _ _ _ _ => rfl) ?_ ?_ S S' h c b hset
  · intro S T U hST hTU c b hset
    have h1 := hST c b hset
    rw [hTU c b (by rw [h1]; exact hset), h1]
  · intro S r S' hadd c b hset
    exact addRoot_no_overwrite hadd hset

/-! ### The log -/

lemma addRoots_wellFormed {S₀ S : State} {rs : List InteropRoot} (h : addRoots S₀ rs = some S) :
    ∀ r ∈ rs, r.sides.length = 1 ∧ r.sides.headD 0 ≠ 0 ∧ r.timestamp ≠ 0 := by
  induction rs generalizing S₀ with
  | nil => intro r hr; simp at hr
  | cons x xs ih =>
    obtain ⟨S₁, h1, h2⟩ := addRoots_cons_eq_some.mp h
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · obtain ⟨root, hsides, hroot, hts, -, -⟩ := addRoot_iff.mp h1
      rw [hsides]
      exact ⟨rfl, hroot, hts⟩
    · exact ih h2 r hr

/-- After an import its key holds a nonzero root. -/
lemma addRoot_key_set {S S' : State} {r : InteropRoot} (h : addRoot S r = some S') :
    S'.storedInteropRoots r.chainId r.blockOrBatchNumber = r.stored ∧
    (S'.storedInteropRoots r.chainId r.blockOrBatchNumber).root ≠ 0 := by
  obtain ⟨root, hsides, hroot, -, -, rfl⟩ := addRoot_iff.mp h
  rw [writeRoot_stored_self]
  simp [InteropRoot.stored, hsides, hroot]

lemma addRoot_other_key {S S' : State} {r : InteropRoot} (h : addRoot S r = some S')
    {c b : UInt256} (hne : r.key ≠ (c, b)) :
    S'.storedInteropRoots c b = S.storedInteropRoots c b := by
  obtain ⟨root, -, -, -, -, rfl⟩ := addRoot_iff.mp h
  exact writeRoot_stored_ne S _ _ (fun heq => hne heq.symm)

lemma addRoots_keys {S₀ S : State} {rs : List InteropRoot} (h : addRoots S₀ rs = some S) :
    (rs.map InteropRoot.key).Nodup ∧
    ∀ r ∈ rs, (S₀.storedInteropRoots r.chainId r.blockOrBatchNumber).root = 0 := by
  induction rs generalizing S₀ with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨S₁, h1, h2⟩ := addRoots_cons_eq_some.mp h
    obtain ⟨hnodup, hunset⟩ := ih h2
    have hxset := (addRoot_key_set h1).2
    have hfresh : ∀ r ∈ xs, r.key ≠ x.key := by
      intro r hr heq
      have := hunset r hr
      obtain ⟨hc, hb⟩ := Prod.mk.inj heq
      rw [hc, hb] at this
      exact hxset this
    refine ⟨?_, ?_⟩
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, hnodup⟩
      intro hmem
      obtain ⟨r, hr, heq⟩ := List.mem_map.mp hmem
      exact hfresh r hr heq
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact (addRoot_iff.mp h1).choose_spec.2.2.2.1
      · rw [← addRoot_other_key h1 (fun heq => hfresh r hr heq.symm)]
        exact hunset r hr

lemma addRoots_storage {S₀ S : State} {rs : List InteropRoot} (h : addRoots S₀ rs = some S)
    (c b : UInt256) :
    (∀ r ∈ rs, r.key = (c, b) → S.storedInteropRoots c b = r.stored) ∧
    ((∀ r ∈ rs, r.key ≠ (c, b)) → S.storedInteropRoots c b = S₀.storedInteropRoots c b) := by
  induction rs generalizing S₀ with
  | nil =>
    obtain rfl : S₀ = S := by simpa [addRoots] using h
    simp
  | cons x xs ih =>
    obtain ⟨S₁, h1, h2⟩ := addRoots_cons_eq_some.mp h
    obtain ⟨ihhit, ihmiss⟩ := ih h2
    refine ⟨?_, ?_⟩
    · intro r hr hkey
      rcases List.mem_cons.mp hr with rfl | hr
      · have hmiss : ∀ r' ∈ xs, r'.key ≠ (c, b) := by
          intro r' hr' heq
          have hun := (addRoots_keys h2).2 r' hr'
          obtain ⟨hc, hb⟩ := Prod.mk.inj heq
          obtain ⟨hc', hb'⟩ := Prod.mk.inj hkey
          rw [hc, hb, ← hc', ← hb'] at hun
          exact (addRoot_key_set h1).2 hun
        rw [ihmiss hmiss]
        obtain ⟨hc', hb'⟩ := Prod.mk.inj hkey
        rw [← hc', ← hb']
        exact (addRoot_key_set h1).1
      · exact ihhit r hr hkey
    · intro hmiss
      rw [ihmiss (fun r hr => hmiss r (List.mem_cons_of_mem _ hr))]
      exact addRoot_other_key h1 (hmiss x List.mem_cons_self)

theorem logged_imports_well_formed {S₀ S : State} {log : List (Address × Call)}
    (h : ReachLog S₀ S log) :
    ∀ r ∈ imports log, r.sides.length = 1 ∧ r.sides.headD 0 ≠ 0 ∧ r.timestamp ≠ 0 :=
  addRoots_wellFormed (reachLog_addRoots h)

theorem each_key_imported_once {S₀ S : State} {log : List (Address × Call)}
    (h : ReachLog S₀ S log) :
    ((imports log).map InteropRoot.key).Nodup ∧
    ∀ r ∈ imports log, (S₀.storedInteropRoots r.chainId r.blockOrBatchNumber).root = 0 :=
  addRoots_keys (reachLog_addRoots h)

theorem storage_is_the_log {S₀ S : State} {log : List (Address × Call)}
    (h : ReachLog S₀ S log) (c b : UInt256) :
    (∀ r ∈ imports log, r.key = (c, b) → S.storedInteropRoots c b = r.stored) ∧
    ((∀ r ∈ imports log, r.key ≠ (c, b)) → S.storedInteropRoots c b = S₀.storedInteropRoots c b) :=
  addRoots_storage (reachLog_addRoots h) c b

theorem stored_iff_imported {S : State} {log : List (Address × Call)}
    (h : ReachLog empty S log) (c b : UInt256) :
    (S.storedInteropRoots c b).root ≠ 0 ↔ ∃ r ∈ imports log, r.key = (c, b) := by
  obtain ⟨hhit, hmiss⟩ := storage_is_the_log h c b
  constructor
  · intro hset
    by_contra hnone
    push Not at hnone
    exact hset (by rw [hmiss hnone]; rfl)
  · rintro ⟨r, hr, hkey⟩
    rw [hhit r hr hkey]
    exact (logged_imports_well_formed h r hr).2.1

/-! ### Timestamps -/

lemma addRoot_zeroTimestampIffUnset {S S' : State} {r : InteropRoot} (h : addRoot S r = some S')
    (hinv : ZeroTimestampIffUnset S) : ZeroTimestampIffUnset S' := by
  obtain ⟨root, -, hroot, hts, -, rfl⟩ := addRoot_iff.mp h
  intro c b
  by_cases hkey : (c, b) = (r.chainId, r.blockOrBatchNumber)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkey
    rw [writeRoot_stored_self]
    exact ⟨fun h0 => absurd h0 hroot, fun h0 => absurd h0 hts⟩
  · rw [writeRoot_stored_ne S _ _ hkey]
    exact hinv c b

theorem zero_timestamp_iff_unset_invariant :
    ZeroTimestampIffUnset empty ∧
    ∀ (S S' : State), Reach S S' → ZeroTimestampIffUnset S → ZeroTimestampIffUnset S' :=
  ⟨fun _ _ => Iff.rfl,
   reach_of_addRoot_rel (fun S S' => ZeroTimestampIffUnset S → ZeroTimestampIffUnset S')
    (fun _ h => h) (fun _ _ _ h1 h2 h => h2 (h1 h))
    (fun _ _ _ hadd => addRoot_zeroTimestampIffUnset hadd)⟩

lemma addRoot_latestIsMax {S S' : State} {r : InteropRoot} (h : addRoot S r = some S')
    (hinv : LatestIsMax S) : LatestIsMax S' := by
  obtain ⟨hbound, hattained⟩ := hinv
  obtain ⟨root, -, hroot, -, hunset, rfl⟩ := addRoot_iff.mp h
  refine ⟨?_, ?_⟩
  · intro c b
    by_cases hkey : (c, b) = (r.chainId, r.blockOrBatchNumber)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkey
      rw [writeRoot_stored_self, writeRoot_latest_self]
      exact le_max_right _ _
    · rw [writeRoot_stored_ne S _ _ hkey]
      exact le_trans (hbound c b) (le_writeRoot_latest ..)
  · intro c hne
    by_cases hc : c = r.chainId
    · subst hc
      rw [writeRoot_latest_self] at hne ⊢
      by_cases hlt : S.latestInteropRootTimestamp r.chainId < r.timestamp
      · refine ⟨r.blockOrBatchNumber, ?_, ?_⟩
        · rw [writeRoot_stored_self]; exact hroot
        · rw [writeRoot_stored_self, max_eq_right hlt.le]
      · rw [max_eq_left (not_lt.mp hlt)] at hne ⊢
        obtain ⟨b, hb, hbts⟩ := hattained r.chainId hne
        have hkey : (r.chainId, b) ≠ (r.chainId, r.blockOrBatchNumber) := by
          intro heq
          obtain ⟨-, rfl⟩ := Prod.mk.inj heq
          exact hb hunset
        exact ⟨b, by rw [writeRoot_stored_ne S _ _ hkey]; exact hb,
          by rw [writeRoot_stored_ne S _ _ hkey]; exact hbts⟩
    · rw [writeRoot_latest_ne S _ _ _ hc] at hne ⊢
      obtain ⟨b, hb, hbts⟩ := hattained c hne
      have hkey : (c, b) ≠ (r.chainId, r.blockOrBatchNumber) := by
        intro heq
        exact hc (Prod.mk.inj heq).1
      exact ⟨b, by rw [writeRoot_stored_ne S _ _ hkey]; exact hb,
        by rw [writeRoot_stored_ne S _ _ hkey]; exact hbts⟩

theorem latest_is_max_invariant :
    LatestIsMax empty ∧ ∀ (S S' : State), Reach S S' → LatestIsMax S → LatestIsMax S' :=
  ⟨⟨fun _ _ => le_refl _, fun _ h => absurd rfl h⟩,
   reach_of_addRoot_rel (fun S S' => LatestIsMax S → LatestIsMax S')
    (fun _ h => h) (fun _ _ _ h1 h2 h => h2 (h1 h))
    (fun _ _ _ hadd => addRoot_latestIsMax hadd)⟩

lemma addRoot_latest_le {S S' : State} {r : InteropRoot} (h : addRoot S r = some S') (c : UInt256) :
    S.latestInteropRootTimestamp c ≤ S'.latestInteropRootTimestamp c := by
  obtain ⟨root, -, -, -, -, rfl⟩ := addRoot_iff.mp h
  exact le_writeRoot_latest ..

lemma addRoots_latest_le {S S' : State} {rs : List InteropRoot} (h : addRoots S rs = some S')
    (c : UInt256) : S.latestInteropRootTimestamp c ≤ S'.latestInteropRootTimestamp c :=
  addRoots_rel (fun S S' => ∀ c, S.latestInteropRootTimestamp c ≤ S'.latestInteropRootTimestamp c)
    (fun _ _ => le_refl _) (fun _ _ _ h1 h2 c => le_trans (h1 c) (h2 c))
    (fun _ _ _ hadd c => addRoot_latest_le hadd c) rs S S' h c

theorem latest_never_decreases {S S' : State} (h : Reach S S') (c : UInt256) :
    S.latestInteropRootTimestamp c ≤ S'.latestInteropRootTimestamp c :=
  reach_of_addRoot_rel
    (fun S S' => ∀ c, S.latestInteropRootTimestamp c ≤ S'.latestInteropRootTimestamp c)
    (fun _ _ => le_refl _) (fun _ _ _ h1 h2 c => le_trans (h1 c) (h2 c))
    (fun _ _ _ hadd c => addRoot_latest_le hadd c) S S' h c

lemma addRoots_latest_bounds {S₀ S : State} {rs : List InteropRoot} (h : addRoots S₀ rs = some S) :
    ∀ r ∈ rs, r.timestamp ≤ S.latestInteropRootTimestamp r.chainId := by
  induction rs generalizing S₀ with
  | nil => intro r hr; simp at hr
  | cons x xs ih =>
    obtain ⟨S₁, h1, h2⟩ := addRoots_cons_eq_some.mp h
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · refine le_trans ?_ (addRoots_latest_le h2 _)
      obtain ⟨root, -, -, -, -, rfl⟩ := addRoot_iff.mp h1
      rw [writeRoot_latest_self]
      exact le_max_right _ _
    · exact ih h2 r hr

theorem latest_bounds_every_import {S₀ S : State} {log : List (Address × Call)}
    (h : ReachLog S₀ S log) :
    ∀ r ∈ imports log, r.timestamp ≤ S.latestInteropRootTimestamp r.chainId :=
  addRoots_latest_bounds (reachLog_addRoots h)

theorem latest_zero_iff_nothing_imported {S : State} (h : Reach empty S) (c : UInt256) :
    S.latestInteropRootTimestamp c = 0 ↔ ∀ b, (S.storedInteropRoots c b).root = 0 := by
  have hz := zero_timestamp_iff_unset_invariant.2 _ _ h zero_timestamp_iff_unset_invariant.1
  obtain ⟨hbound, hattained⟩ := latest_is_max_invariant.2 _ _ h latest_is_max_invariant.1
  constructor
  · intro h0 b
    refine (hz c b).mpr ?_
    have := hbound c b
    rw [h0] at this
    exact le_antisymm this (Fin.zero_le _)
  · intro hall
    by_contra hne
    obtain ⟨b, hb, -⟩ := hattained c hne
    exact hb (hall b)

/-! ### Batches -/

theorem batch_unfolds_to_singles (S : State) :
    addInteropRootsInBatch S L2_BOOTLOADER_ADDRESS [] = some S ∧
    ∀ (r : InteropRoot) (rs : List InteropRoot),
      addInteropRootsInBatch S L2_BOOTLOADER_ADDRESS (r :: rs) =
        (addSingleInteropRoot S L2_BOOTLOADER_ADDRESS r).bind
          (fun S' => addInteropRootsInBatch S' L2_BOOTLOADER_ADDRESS rs) := by
  refine ⟨by simp [addInteropRootsInBatch, addRoots], ?_⟩
  intro r rs
  simp only [addInteropRootsInBatch, addSingleInteropRoot, addRoots, ne_eq, not_true_eq_false,
    ite_false]
  cases addRoot S r <;> rfl

theorem batch_rejects_duplicate_key (S : State) (caller : Address) (rs : List InteropRoot)
    (hdup : ¬ (rs.map InteropRoot.key).Nodup) : addInteropRootsInBatch S caller rs = none := by
  unfold addInteropRootsInBatch
  split_ifs
  · rfl
  · rw [Option.eq_none_iff_forall_ne_some]
    intro S' h
    exact hdup (addRoots_keys h).1

/-! ### Countermodels -/

theorem without_auth_anyone_squats_a_key : Properties.WithoutAuthAnyoneSquatsAKey := by
  refine ⟨0x1234, ⟨1, 100, 5, [0xbad]⟩, ⟨1, 100, 50, [0xaa]⟩, writeRoot empty 1 100 5 0xbad,
    by decide, rfl, by decide, ?_, ?_, ?_, ?_⟩
  · have : addSingleInteropRoot empty L2_BOOTLOADER_ADDRESS ⟨1, 100, 50, [0xaa]⟩
        = some (writeRoot empty 1 100 50 0xaa) := by
      unfold addSingleInteropRoot
      rw [if_neg (by simp)]
      exact addRoot_mk (by decide) (by decide) rfl
    rw [this]
    exact Option.some_ne_none _
  · unfold addSingleInteropRoot
    exact if_pos (by decide)
  · exact addRoot_mk (by decide) (by decide) rfl
  · intro S' hreach
    have hset : ((writeRoot empty 1 100 5 0xbad).storedInteropRoots 1 100).root ≠ 0 := by
      rw [writeRoot_stored_self]; decide
    have hkeep := no_overwrite hreach hset
    rw [writeRoot_stored_self] at hkeep
    refine ⟨hkeep, ?_⟩
    rw [Option.eq_none_iff_forall_ne_some]
    intro S'' hexec
    obtain ⟨-, hadd⟩ := exec_eq_some.mp hexec
    rw [Call.roots, addRoots_singleton] at hadd
    obtain ⟨root, -, -, -, hunset, -⟩ := addRoot_iff.mp hadd
    rw [hkeep] at hunset
    exact absurd hunset (by decide)

theorem without_exists_check_root_is_overwritten : Properties.WithoutExistsCheckRootIsOverwritten := by
  refine ⟨writeRoot empty 1 100 50 0xaa, writeRoot (writeRoot empty 1 100 50 0xaa) 1 100 60 0xbb,
    1, 100, 50, 60, 0xaa, 0xbb, ?_, writeRoot_stored_self .., by decide, ?_, ?_,
    writeRoot_stored_self ..⟩
  · exact reach_of_addRoot (addRoot_mk (c := 1) (b := 100) (ts := 50) (root := 0xaa)
      (by decide) (by decide) rfl)
  · rw [Option.eq_none_iff_forall_ne_some]
    intro S' h
    obtain ⟨root, -, -, -, hunset, -⟩ := addInteropRoot_iff.mp h
    rw [writeRoot_stored_self] at hunset
    exact absurd hunset (by decide)
  · unfold addInteropRootNoExistsCheck
    rw [if_neg (by simp), if_neg (by decide), if_neg (by decide)]
    rfl

theorem without_zero_root_check_timestamp_is_rewritten :
    Properties.WithoutZeroRootCheckTimestampIsRewritten := by
  refine ⟨writeRoot empty 1 100 5 0, writeRoot (writeRoot empty 1 100 5 0) 1 100 7 1, 1, 100,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [addInteropRoot]
  · unfold addInteropRootNoZeroRootCheck
    rw [if_neg (by simp), if_neg (by decide), if_neg (by simp [empty])]
    rfl
  · intro hinv
    have := (hinv 1 100).mp (by rw [writeRoot_stored_self])
    rw [writeRoot_stored_self] at this
    exact absurd this (by decide)
  · rw [writeRoot_stored_self]
  · exact addInteropRoot_iff.mpr ⟨1, rfl, by decide, by decide, by rw [writeRoot_stored_self], rfl⟩
  · rw [writeRoot_stored_self]

theorem without_zero_timestamp_check_root_looks_unimported :
    Properties.WithoutZeroTimestampCheckRootLooksUnimported := by
  refine ⟨writeRoot empty 1 100 0 1, 1, 100, ?_, ?_, ?_⟩
  · simp [addInteropRoot]
  · unfold addInteropRootNoZeroTimestampCheck
    rw [if_neg (by simp), if_neg (by decide), if_neg (by simp [empty])]
    rfl
  · intro S' hreach
    have hset : ((writeRoot empty 1 100 0 1).storedInteropRoots 1 100).root ≠ 0 := by
      rw [writeRoot_stored_self]; decide
    rw [no_overwrite hreach hset, writeRoot_stored_self]
    exact ⟨by decide, rfl⟩

theorem legacy_root_breaks_zero_timestamp_claim : Properties.LegacyRootBreaksZeroTimestampClaim := by
  refine ⟨⟨fun c b => if c = 1 ∧ b = 100 then ⟨0xaa, 0⟩ else ⟨0, 0⟩, fun _ => 0⟩, ?_⟩
  intro S' hreach hinv
  have hkeep := no_overwrite hreach (c := 1) (b := 100) (by simp)
  have h0 := (hinv 1 100).mpr (by rw [hkeep]; simp)
  rw [hkeep] at h0
  simp at h0

/-! ### Non-vacuity -/

theorem concrete_run : Properties.ConcreteRun := by
  let S₁ := writeRoot empty 9 7 5 0xdd
  let S₂ := writeRoot (writeRoot (writeRoot S₁ 1 100 50 0xaa) 1 101 70 0xbb) 1 99 60 0xcc
  have h1 : exec empty L2_BOOTLOADER_ADDRESS (.single ⟨9, 7, 5, [0xdd]⟩) = some S₁ := by
    refine exec_eq_some.mpr ⟨rfl, ?_⟩
    rw [Call.roots, addRoots_singleton]
    exact addRoot_mk (by decide) (by decide) rfl
  have h2 : exec S₁ L2_BOOTLOADER_ADDRESS
      (.batch [⟨1, 100, 50, [0xaa]⟩, ⟨1, 101, 70, [0xbb]⟩, ⟨1, 99, 60, [0xcc]⟩]) = some S₂ := by
    refine exec_eq_some.mpr ⟨rfl, ?_⟩
    refine addRoots_cons_eq_some.mpr ⟨_, addRoot_mk (by decide) (by decide) (by decide), ?_⟩
    refine addRoots_cons_eq_some.mpr ⟨_, addRoot_mk (by decide) (by decide) (by decide), ?_⟩
    refine addRoots_cons_eq_some.mpr ⟨_, addRoot_mk (by decide) (by decide) (by decide), rfl⟩
  refine ⟨S₂, _, ReachLog.tail _ _ (ReachLog.tail _ _ ReachLog.refl h1) h2, rfl, rfl,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ### The named properties -/

theorem AddInteropRootIff : Properties.AddInteropRootIff :=
  fun _ _ _ _ _ _ => addInteropRoot_iff
theorem AddInteropRootEffect : Properties.AddInteropRootEffect :=
  fun _ _ _ _ _ _ h => add_interop_root_effect h
theorem OnlyBootloaderWrites : Properties.OnlyBootloaderWrites :=
  fun _ _ _ _ h => only_bootloader_writes h
theorem ReachIffReachLog : Properties.ReachIffReachLog := fun _ _ => reach_iff_reachLog
theorem LoggedCallersAreBootloader : Properties.LoggedCallersAreBootloader :=
  fun _ _ _ h => logged_callers_are_bootloader h
theorem NoOverwrite : Properties.NoOverwrite := fun _ _ _ _ h hset => no_overwrite h hset
theorem LoggedImportsWellFormed : Properties.LoggedImportsWellFormed :=
  fun _ _ _ h => logged_imports_well_formed h
theorem EachKeyImportedOnce : Properties.EachKeyImportedOnce :=
  fun _ _ _ h => each_key_imported_once h
theorem StorageIsTheLog : Properties.StorageIsTheLog := fun _ _ _ h c b => storage_is_the_log h c b
theorem StoredIffImported : Properties.StoredIffImported := fun _ _ h c b => stored_iff_imported h c b
theorem ZeroTimestampIffUnsetInvariant : Properties.ZeroTimestampIffUnsetInvariant :=
  zero_timestamp_iff_unset_invariant
theorem LatestIsMaxInvariant : Properties.LatestIsMaxInvariant := latest_is_max_invariant
theorem LatestNeverDecreases : Properties.LatestNeverDecreases :=
  fun _ _ c h => latest_never_decreases h c
theorem LatestBoundsEveryImport : Properties.LatestBoundsEveryImport :=
  fun _ _ _ h => latest_bounds_every_import h
theorem LatestZeroIffNothingImported : Properties.LatestZeroIffNothingImported :=
  fun _ h c => latest_zero_iff_nothing_imported h c
theorem BatchUnfoldsToSingles : Properties.BatchUnfoldsToSingles := batch_unfolds_to_singles
theorem BatchRejectsDuplicateKey : Properties.BatchRejectsDuplicateKey := batch_rejects_duplicate_key
theorem WithoutAuthAnyoneSquatsAKey : Properties.WithoutAuthAnyoneSquatsAKey :=
  without_auth_anyone_squats_a_key
theorem WithoutExistsCheckRootIsOverwritten : Properties.WithoutExistsCheckRootIsOverwritten :=
  without_exists_check_root_is_overwritten
theorem WithoutZeroRootCheckTimestampIsRewritten :
    Properties.WithoutZeroRootCheckTimestampIsRewritten :=
  without_zero_root_check_timestamp_is_rewritten
theorem WithoutZeroTimestampCheckRootLooksUnimported :
    Properties.WithoutZeroTimestampCheckRootLooksUnimported :=
  without_zero_timestamp_check_root_looks_unimported
theorem LegacyRootBreaksZeroTimestampClaim : Properties.LegacyRootBreaksZeroTimestampClaim :=
  legacy_root_breaks_zero_timestamp_claim
theorem ConcreteRun : Properties.ConcreteRun := concrete_run

end Contracts.InteropRootStorage
