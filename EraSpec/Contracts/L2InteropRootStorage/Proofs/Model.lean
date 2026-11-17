import EraSpec.Contracts.L2InteropRootStorage.Properties.Model

/-!
# Proofs: imported roots are write-once, and a zero timestamp means absent

Every write is behind `fresh` (the stored root is `0`), so an entry with a nonzero root is never
written again; and every write stores a nonzero root with a nonzero timestamp, so from fresh
storage the two are zero together.
-/

namespace Contracts.L2InteropRootStorage

theorem write_entries (st : State) (x : RootIn) (r : Word) (c : ChainId) (n : ℕ) :
    (st.write x r).entries c n =
      if c = x.chainId ∧ n = x.blockOrBatchNumber then ⟨r, x.ts⟩ else st.entries c n := by
  unfold State.write
  by_cases hc : c = x.chainId
  · subst hc
    by_cases hn : n = x.blockOrBatchNumber
    · subst hn; simp
    · simp [hn]
  · simp [hc]

theorem write_frozen {st : State} {x : RootIn} {r : Word} (hg : AddGuard st x r) {c : ChainId}
    {n : ℕ} (h : (st.entries c n).root ≠ 0) : (st.write x r).entries c n = st.entries c n := by
  rw [write_entries]
  split_ifs with hk
  · obtain ⟨rfl, rfl⟩ := hk
    exact absurd hg.fresh h
  · rfl

theorem addsAll_frozen {ok : RootIn → Prop} {st st' : State} {xs : List RootIn}
    (h : AddsAll ok st xs st') {c : ChainId} {n : ℕ} (hne : (st.entries c n).root ≠ 0) :
    st'.entries c n = st.entries c n := by
  induction h with
  | nil => rfl
  | cons r _ hg _ ih =>
    rw [ih (by rw [write_frozen hg hne]; exact hne), write_frozen hg hne]

theorem step_frozen {ok : RootIn → Prop} {st st' : State} (hs : Step ok st st') {c : ChainId}
    {n : ℕ} (hne : (st.entries c n).root ≠ 0) : st'.entries c n = st.entries c n := by
  cases hs with
  | single x r _ hg => exact write_frozen hg hne
  | batch xs h => exact addsAll_frozen h hne

theorem reach_frozen {ok : RootIn → Prop} {st st' : State} (hr : Reach ok st st') {c : ChainId}
    {n : ℕ} (hne : (st.entries c n).root ≠ 0) : st'.entries c n = st.entries c n := by
  induction hr with
  | refl => rfl
  | tail _ hs ih => rw [step_frozen hs (by rw [ih]; exact hne), ih]

/-! ## The invariant from fresh storage -/

/-- From fresh storage: zero together, and every nonzero entry is an admitted import. -/
def StorageInv (ok : RootIn → Prop) (st : State) : Prop :=
  ∀ c n, ((st.entries c n).ts = 0 ↔ (st.entries c n).root = 0) ∧
    ((st.entries c n).root ≠ 0 → ∃ (x : RootIn) (r : Word), ok x ∧ x.chainId = c
      ∧ x.blockOrBatchNumber = n ∧ x.sides = [r] ∧ st.entries c n = ⟨r, x.ts⟩)

theorem storageInv_empty (ok : RootIn → Prop) : StorageInv ok empty := by
  intro c n
  simp [empty]

theorem storageInv_write {ok : RootIn → Prop} {st : State} {x : RootIn} {r : Word}
    (hI : StorageInv ok st) (hok : ok x) (hg : AddGuard st x r) : StorageInv ok (st.write x r) := by
  intro c n
  rw [write_entries]
  split_ifs with hk
  · obtain ⟨rfl, rfl⟩ := hk
    refine ⟨⟨fun h => absurd h hg.tsNonzero, fun h => absurd h hg.nonzero⟩, fun _ => ?_⟩
    exact ⟨x, r, hok, rfl, rfl, hg.sides, rfl⟩
  · exact hI c n

theorem storageInv_addsAll {ok : RootIn → Prop} {st st' : State} {xs : List RootIn}
    (h : AddsAll ok st xs st') (hI : StorageInv ok st) : StorageInv ok st' := by
  induction h with
  | nil => exact hI
  | cons r hok hg _ ih => exact ih (storageInv_write hI hok hg)

theorem storageInv_reach {ok : RootIn → Prop} {st : State} (hr : Reach ok empty st) :
    StorageInv ok st := by
  induction hr with
  | refl => exact storageInv_empty ok
  | tail _ hs ih =>
    cases hs with
    | single x r hok hg => exact storageInv_write ih hok hg
    | batch xs h => exact storageInv_addsAll h ih

/-! ## The properties -/

theorem WriteOnce : Properties.WriteOnce :=
  fun _ _ _ hr _ _ hne => reach_frozen hr hne

theorem TimestampNotRewritable : Properties.TimestampNotRewritable := by
  intro ok st st' h0 hr c n hts
  have hroot : (st.entries c n).root ≠ 0 := fun h => hts (((storageInv_reach h0) c n).1.mpr h)
  exact reach_frozen hr hroot

theorem ZeroTimestampIffAbsent : Properties.ZeroTimestampIffAbsent :=
  fun _ _ h0 c n => ((storageInv_reach h0) c n).1

theorem EntriesAreAdmittedImports : Properties.EntriesAreAdmittedImports :=
  fun _ _ h0 c n hne => ((storageInv_reach h0) c n).2 hne

theorem BatchImportWritesEach : Properties.BatchImportWritesEach := by
  intro ok st st' xs h
  induction h with
  | nil => intro x hx; simp at hx
  | @cons st₀ st₁ x xs r hok hg htail ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · refine ⟨hok, r, hg.sides, ?_⟩
      have hw : (st₀.write y r).entries y.chainId y.blockOrBatchNumber = ⟨r, y.ts⟩ := by
        rw [write_entries]; simp
      rw [addsAll_frozen htail (by rw [hw]; exact hg.nonzero), hw]
    · exact ih y hy

theorem BatchKeysDistinct : Properties.BatchKeysDistinct := by
  intro ok st st' xs h
  induction h with
  | nil => simp
  | @cons st₀ st₁ x xs r hok hg htail ih =>
    obtain ⟨hnd, hfresh⟩ := ih
    have hw : (st₀.write x r).entries x.chainId x.blockOrBatchNumber = ⟨r, x.ts⟩ := by
      rw [write_entries]; simp
    have hkey : ∀ y ∈ xs, (y.chainId, y.blockOrBatchNumber) ≠ (x.chainId, x.blockOrBatchNumber) := by
      intro y hy hyx
      simp only [Prod.mk.injEq] at hyx
      have := hfresh y hy
      rw [hyx.1, hyx.2, hw] at this
      exact hg.nonzero this
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
      exact ⟨fun y hy he => hkey y hy he, hnd⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hg.fresh
      · have h1 := hfresh y hy
        rw [write_entries] at h1
        split_ifs at h1 with hk
        · exact absurd (by rw [hk.1, hk.2]) (hkey y hy)
        · exact h1

theorem LegacyEntryBlocksTimeoutForever : Properties.LegacyEntryBlocksTimeoutForever := by
  intro ok st₀ st c n r hr h0 hrun
  have hst : st.entries c n = ⟨r, 0⟩ := by
    rw [reach_frozen hrun (by rw [h0]; exact hr), h0]
  refine ⟨⟨by rw [hst], by rw [hst]; exact hr⟩, fun D hpass => hpass.1 (by rw [hst])⟩

/-- The legacy storage: one v31-format entry `(1, 0)` at `(1, 1)`. -/
def legacyStorage : State := ⟨fun c n => if c = 1 ∧ n = 1 then ⟨1, 0⟩ else ⟨0, 0⟩⟩

/-- A fresh import of root `2` at `(1, 2)` with timestamp `5`. -/
def legacyFreshImport : RootIn := ⟨1, 2, 5, [2]⟩

theorem LegacyEntryCountermodel : Properties.LegacyEntryCountermodel := by
  have hg : AddGuard legacyStorage legacyFreshImport 2 :=
    ⟨rfl, by decide, by decide, by simp [legacyStorage, legacyFreshImport]⟩
  have hrun : Reach (fun _ => True) legacyStorage (legacyStorage.write legacyFreshImport 2) :=
    Reach.tail Reach.refl (Step.single legacyFreshImport 2 trivial hg)
  obtain ⟨hinc, hto⟩ := LegacyEntryBlocksTimeoutForever (fun _ => True) legacyStorage _ 1 1 1
    (by decide) (by simp [legacyStorage]) hrun
  refine ⟨legacyStorage, _, 1, 1, 2, 1, by decide, by simp [legacyStorage], hrun, hinc, hto, ?_⟩
  have hw : (legacyStorage.write legacyFreshImport 2).entries 1 2 = ⟨2, 5⟩ := by
    rw [write_entries]; simp [legacyFreshImport]
  refine ⟨by rw [hw]; decide, by rw [hw]; decide⟩

theorem StorageWitness : Properties.StorageWitness := by
  let x : RootIn := ⟨1, 1, 5, [3]⟩
  let y : RootIn := ⟨1, 2, 6, [4]⟩
  have hx : AddGuard empty x 3 := ⟨rfl, by decide, by decide, rfl⟩
  have hy : AddGuard (empty.write x 3) y 4 :=
    ⟨rfl, by decide, by decide, by rw [write_entries]; simp [x, y, empty]⟩
  have hrun : AddsAll (fun _ => True) empty [x, y] ((empty.write x 3).write y 4) :=
    AddsAll.cons 3 trivial hx (AddsAll.cons 4 trivial hy AddsAll.nil)
  refine ⟨_, [x, y], hrun, rfl, ?_⟩
  intro z hz
  obtain ⟨-, r, -, hst⟩ := BatchImportWritesEach _ _ _ _ hrun z hz
  rw [hst]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl <;> simp [x, y]

end Contracts.L2InteropRootStorage
