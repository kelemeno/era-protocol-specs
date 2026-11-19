import EraSpec.Contracts.L2InteropRootStorage.History.Properties.AtC67894b9
import EraSpec.Contracts.L2InteropRootStorage.Proofs.Storage

/-!
# History proofs: `L2InteropRootStorage` at `c67894b9`

The `c67894b9` contract is the canonical model's projection call by call (`execAtC67_eq`); runs
lift and project (`reachAtC67_lifts`, `reach_projects`), so the `c67894b9` results follow from the
canonical model's. `ImportsGrow` is `no_overwrite_at_c67894b9` read through `importWorldAtC67`.
-/

namespace Contracts.InteropRootStorage.History

lemma addInteropRootAtC67_eq (S : State) (chainId blockOrBatchNumber timestamp : UInt256)
    (sides : List UInt256) :
    addInteropRootAtC67 S.storedInteropRoots chainId blockOrBatchNumber timestamp sides =
      (addInteropRoot S chainId blockOrBatchNumber timestamp sides).map State.storedInteropRoots := by
  unfold addInteropRootAtC67 addInteropRoot
  split_ifs <;> rfl

lemma addRootsAtC67_eq (rs : List InteropRoot) (S : State) :
    addRootsAtC67 S.storedInteropRoots rs = (addRoots S rs).map State.storedInteropRoots := by
  induction rs generalizing S with
  | nil => rfl
  | cons r rs ih =>
    have h := addInteropRootAtC67_eq S r.chainId r.blockOrBatchNumber r.timestamp r.sides
    simp only [addRootsAtC67, addRoots, addRoot]
    rw [h]
    cases addInteropRoot S r.chainId r.blockOrBatchNumber r.timestamp r.sides with
    | none => rfl
    | some S₁ => exact ih S₁

lemma execAtC67_eq (S : State) (caller : Address) (c : Call) :
    execAtC67 S.storedInteropRoots caller c = (exec S caller c).map State.storedInteropRoots := by
  cases c with
  | single r =>
    simp only [execAtC67, exec, addSingleInteropRoot, Call.roots]
    split_ifs
    · rfl
    · rw [addRootsAtC67_eq, addRoots_singleton]
  | batch rs =>
    simp only [execAtC67, exec, addInteropRootsInBatch, Call.roots]
    split_ifs
    · rfl
    · exact addRootsAtC67_eq rs S

lemma reach_projects {S S' : State} (h : Reach S S') :
    ReachAtC67 S.storedInteropRoots S'.storedInteropRoots := by
  induction h with
  | refl => exact ReachAtC67.refl
  | tail _ hstep ih =>
    obtain ⟨caller, c, hexec⟩ := hstep
    exact ReachAtC67.tail caller c ih (by rw [execAtC67_eq, hexec]; rfl)

lemma reachAtC67_lifts {R R' : RootsAtC67} (h : ReachAtC67 R R') (L : UInt256 → UInt256) :
    ∃ L', Reach ⟨R, L⟩ ⟨R', L'⟩ := by
  induction h with
  | refl => exact ⟨L, Reach.refl⟩
  | @tail T U caller c _ hexec ih =>
    obtain ⟨L', hreach⟩ := ih
    have hproj := execAtC67_eq ⟨T, L'⟩ caller c
    rw [hexec] at hproj
    cases hS : exec ⟨T, L'⟩ caller c with
    | none => rw [hS] at hproj; exact absurd hproj (by simp)
    | some S'' =>
      rw [hS] at hproj
      obtain rfl : _ = S''.storedInteropRoots := Option.some.inj hproj
      exact ⟨S''.latestInteropRootTimestamp, Reach.tail hreach (Step.call caller c hS)⟩

theorem c67894b9_runs_are_projected_runs (R R' : RootsAtC67) :
    ReachAtC67 R R' ↔ ∀ L : UInt256 → UInt256, ∃ L', Reach ⟨R, L⟩ ⟨R', L'⟩ := by
  constructor
  · intro h L
    exact reachAtC67_lifts h L
  · intro h
    obtain ⟨_, hreach⟩ := h (fun _ => 0)
    exact reach_projects hreach

theorem no_overwrite_at_c67894b9 {R R' : RootsAtC67} (h : ReachAtC67 R R') {c b : UInt256}
    (hset : (R c b).root ≠ 0) : R' c b = R c b := by
  obtain ⟨_, hreach⟩ := reachAtC67_lifts h (fun _ => 0)
  exact no_overwrite hreach hset

theorem zero_timestamp_iff_unset_at_c67894b9 {R : RootsAtC67}
    (h : ReachAtC67 empty.storedInteropRoots R) (c b : UInt256) :
    (R c b).root = 0 ↔ (R c b).timestamp = 0 := by
  obtain ⟨_, hreach⟩ := reachAtC67_lifts h (fun _ => 0)
  exact zero_timestamp_iff_unset_invariant.2 _ _ hreach (fun _ _ => Iff.rfl) c b

theorem c67894b9_run_witness : Properties.C67894b9RunWitness := by
  let S₁ := writeRoot empty 9 7 5 0xdd
  have h1 : Reach empty S₁ := reach_of_addRoot (addRoot_mk (by decide) (by decide) rfl)
  have h2 : Reach S₁ (writeRoot S₁ 9 8 6 0xee) :=
    reach_of_addRoot (addRoot_mk (by decide) (by decide) (by decide))
  exact ⟨S₁.storedInteropRoots, (writeRoot S₁ 9 8 6 0xee).storedInteropRoots, reach_projects h1,
    reach_projects h2, by decide, by decide, by decide, by decide⟩

theorem storage_runs_grow_imports_at_c67894b9
    (slRoot : Contracts.Atomicity.Chain → ℕ → Contracts.Timeout.SlRoot)
    (l1 : Contracts.RootImport.Dest → Contracts.Atomicity.Chain)
    (R R' : Contracts.RootImport.Dest → RootsAtC67) (h : ∀ d, ReachAtC67 (R d) (R' d)) :
    Contracts.RootImport.ImportsGrow (importWorldAtC67 slRoot l1 R) (importWorldAtC67 slRoot l1 R') := by
  refine ⟨rfl, rfl, ?_⟩
  intro d sl k himp
  show (R' d sl (Nat.toUInt256 k)).root ≠ 0
  rw [no_overwrite_at_c67894b9 (h d) himp]
  exact himp

theorem storage_runs_grow_imports_witness : Properties.StorageRunsGrowImportsWitnessAtC67894b9 := by
  let S₁ := writeRoot empty 9 7 5 0xdd
  have h1 : Reach empty S₁ := reach_of_addRoot (addRoot_mk (by decide) (by decide) rfl)
  refine ⟨fun _ => empty.storedInteropRoots,
    fun d => if d = 5 then S₁.storedInteropRoots else empty.storedInteropRoots, ?_, ?_⟩
  · intro d
    by_cases hd : d = 5
    · simp only [hd, ite_true]
      exact reach_projects h1
    · simp only [hd, ite_false]
      exact ReachAtC67.refl
  · intro slRoot l1
    exact ⟨fun h => h (show (empty.storedInteropRoots 9 (Nat.toUInt256 7)).root = 0 by decide),
      show (S₁.storedInteropRoots 9 (Nat.toUInt256 7)).root ≠ 0 by decide⟩

theorem C67894b9CallIsTheProjection : Properties.C67894b9CallIsTheProjection := execAtC67_eq
theorem C67894b9RunsAreProjectedRuns : Properties.C67894b9RunsAreProjectedRuns :=
  c67894b9_runs_are_projected_runs
theorem NoOverwriteAtC67894b9 : Properties.NoOverwriteAtC67894b9 :=
  fun _ _ _ _ h hset => no_overwrite_at_c67894b9 h hset
theorem ZeroTimestampIffUnsetAtC67894b9 : Properties.ZeroTimestampIffUnsetAtC67894b9 :=
  fun _ h c b => zero_timestamp_iff_unset_at_c67894b9 h c b
theorem C67894b9RunWitness : Properties.C67894b9RunWitness := c67894b9_run_witness
theorem StorageRunsGrowImportsAtC67894b9 : Properties.StorageRunsGrowImportsAtC67894b9 :=
  storage_runs_grow_imports_at_c67894b9
theorem StorageRunsGrowImportsWitnessAtC67894b9 : Properties.StorageRunsGrowImportsWitnessAtC67894b9 :=
  storage_runs_grow_imports_witness

end Contracts.InteropRootStorage.History
