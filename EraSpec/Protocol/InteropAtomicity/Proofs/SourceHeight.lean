import EraSpec.Protocol.InteropAtomicity.Properties.SourceHeight
import EraSpec.Protocol.InteropAtomicity.Proofs.Atomicity
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.RunHeight

/-!
# Proofs: `Wf.capacity` derived from the runs

Proofs of `EraSpec.Protocol.InteropAtomicity.Properties.SourceHeight`.  The capacity
bound is `fmHeight_capacity` and the run-level dimension bookkeeping is
`hReaches_dims` / `reaches_lifts`, both from
`EraSpec.Contracts.L2InteropCommitmentTree.Proofs.RunHeight`.
-/

namespace Contracts.Atomicity

open IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree

lemma runsWf_reaches {St : Chain → ℕ → HState} {time : Chain → ℕ → ℕ} (hW : RunsWf St time)
    (c : Chain) (n : ℕ) : HReaches hSetup (St c n) := by
  induction n with
  | zero => exact hW.start c
  | succ n ih => exact hReaches_trans ih (hW.batch c n)

theorem runs_heights_from_source {St : Chain → ℕ → HState} {time : Chain → ℕ → ℕ}
    (hW : RunsWf St time) : HeightsFromSource (systemOfRuns St time) := by
  intro c n
  show (St c n).dims.height = fmHeight (St c n).tree.leafCount
  rw [hReaches_dims (runsWf_reaches hW c n)]

theorem wf_of_heights_from_source (S : System) (hstart : ∀ c, Reaches setup (S.tree c 0))
    (hbatch : ∀ c n, Reaches (S.tree c n) (S.tree c (n + 1))) (htime : ∀ c, Monotone (S.time c))
    (hH : HeightsFromSource S) : Wf S :=
  ⟨hstart, hbatch, htime, fun c n => by rw [hH c n]; exact fmHeight_capacity _⟩

theorem wf_of_runs (St : Chain → ℕ → HState) (time : Chain → ℕ → ℕ) (hW : RunsWf St time) :
    Wf (systemOfRuns St time) :=
  wf_of_heights_from_source _ (fun c => hReaches_projects (hW.start c))
    (fun c n => hReaches_projects (hW.batch c n)) hW.timeOrdered (runs_heights_from_source hW)

lemma hSetup_eq_dimsOf : hSetup = ⟨setup, ⟨setup.leafCount, fmHeight setup.leafCount⟩⟩ := by
  unfold hSetup
  rw [setupDims_eq]
  rfl

theorem wf_source_heights_from_runs (S : System) (hS : Wf S) (hH : HeightsFromSource S) :
    ∃ St : Chain → ℕ → HState, RunsWf St S.time ∧ systemOfRuns St S.time = S := by
  obtain ⟨tree, time, height⟩ := S
  refine ⟨fun c n => ⟨tree c n, ⟨(tree c n).leafCount, fmHeight (tree c n).leafCount⟩⟩,
    ⟨fun c => ?_, fun c n => reaches_lifts (hS.batch c n), hS.timeOrdered⟩, ?_⟩
  · rw [hSetup_eq_dimsOf]
    exact reaches_lifts (hS.start c)
  · unfold systemOfRuns
    congr 1
    funext c n
    exact (hH c n).symm

theorem begin_height_from_source (S : System) (hH : HeightsFromSource S) (c : Chain) (n : ℕ) :
    beginHeight S c n = fmHeight (beginTree S c n).leafCount := by
  cases n with
  | zero => rfl
  | succ n => exact hH c n

theorem none_or_all_or_break_pinned_from_runs (h : Hash) (z0 : UInt256) (hl : LeafHash)
    (cv : CommitValue) (fh : FlowHash) (St : Chain → ℕ → HState) (time : Chain → ℕ → ℕ)
    (hW : RunsWf St time) (A : Access) (hDA : DataAvailable h z0 hl (systemOfRuns St time) A)
    (F : Flow) (ev : GateEvidence) :
    FlowFinalizableBy h z0 hl cv (systemOfRuns St time) A F
      ∨ (∀ leg, ¬ ExecutedViaBy h z0 hl cv fh (systemOfRuns St time) F ev leg)
      ∨ PinnedGateBreak h z0 hl cv (systemOfRuns St time) A F ev :=
  NoneOrAllOrBreakPinned h z0 hl cv fh _ (wf_of_runs St time hW) A hDA F ev

/-! ## Anti-vacuity -/

theorem padded_system_from_runs (a b : UInt256) (ha : 0 < a) (hab : a < b) :
    ∃ St : Chain → ℕ → HState, RunsWf St (fun _ n => n)
      ∧ systemOfRuns St (fun _ n => n) = paddedSystem a b := by
  refine ⟨fun c _ => if c = 0 then hThree a b else hSetup, ⟨fun c => ?_, fun _ _ => ?_,
    fun _ _ _ hij => hij⟩, ?_⟩
  · show HReaches hSetup (if c = 0 then hThree a b else hSetup)
    split_ifs
    · exact hThree_reaches ha hab
    · exact HReaches.refl
  · exact HReaches.refl
  · unfold systemOfRuns paddedSystem
    congr 1
    · funext c _
      show (if c = 0 then hThree a b else hSetup).tree = if c = 0 then threeLeafTree a b else setup
      split_ifs <;> rfl
    · funext c _
      show (if c = 0 then hThree a b else hSetup).height = if c = 0 then 2 else 0
      split_ifs <;> rfl

theorem mixed_system_from_runs (a : UInt256) (ha : 0 < a) :
    ∃ St : Chain → ℕ → HState, RunsWf St (fun _ n => n)
      ∧ systemOfRuns St (fun _ n => n) = mixedSystem a := by
  refine ⟨fun c _ => if c = 0 then hInsert hSetup a 0 else hSetup, ⟨fun c => ?_, fun _ _ => ?_,
    fun _ _ _ hij => hij⟩, ?_⟩
  · show HReaches hSetup (if c = 0 then hInsert hSetup a 0 else hSetup)
    split_ifs
    · exact HReaches.tail (HReaches.refl (S := hSetup)) (U := hSetup) (setup_insertGuard ha)
    · exact HReaches.refl
  · exact HReaches.refl
  · unfold systemOfRuns mixedSystem
    congr 1
    · funext c _
      show (if c = 0 then hInsert hSetup a 0 else hSetup).tree
        = if c = 0 then insert setup a 0 else setup
      split_ifs <;> rfl
    · funext c _
      show (if c = 0 then hInsert hSetup a 0 else hSetup).height = if c = 0 then 1 else 0
      split_ifs <;> rfl

theorem none_or_all_or_break_pinned_from_runs_stranded (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ∃ St : Chain → ℕ → HState, RunsWf St (fun _ n => n)
      ∧ DataAvailable h z0 hl (systemOfRuns St (fun _ n => n))
          (honestAccess h z0 hl (systemOfRuns St (fun _ n => n)))
      ∧ ¬ FlowFinalizableBy h z0 hl (fun _ b => b) (systemOfRuns St (fun _ n => n))
            (honestAccess h z0 hl (systemOfRuns St (fun _ n => n))) (mixedFlow 0 1 2)
      ∧ FirstStrandedLeg h z0 hl (fun _ b => b) (systemOfRuns St (fun _ n => n))
            (honestAccess h z0 hl (systemOfRuns St (fun _ n => n))) (mixedFlow 0 1 2) ⟨1, 2⟩
      ∧ ∃ ev : GateEvidence,
          (∀ leg, ¬ ExecutedViaBy h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
              (systemOfRuns St (fun _ n => n)) (mixedFlow 0 1 2) ev leg)
          ∧ ¬ PinnedGateBreak h z0 hl (fun _ b => b) (systemOfRuns St (fun _ n => n))
              (honestAccess h z0 hl (systemOfRuns St (fun _ n => n))) (mixedFlow 0 1 2) ev := by
  have h1 : (0 : UInt256) < 1 := by decide
  obtain ⟨St, hW, hEq⟩ := mixed_system_from_runs 1 h1
  obtain ⟨_, hDA, _, hnf, hfirst, ev, _, _, hnoexec, hnb⟩ :=
    NoneOrAllOrBreakPinnedStrandedNotTautology h z0 hl
  refine ⟨St, hW, ?_⟩
  rw [hEq]
  exact ⟨hDA, hnf, hfirst, ev, hnoexec, hnb⟩

end Contracts.Atomicity

/-! ## Certificates -/

namespace Contracts.Atomicity

theorem WfOfRuns : Properties.WfOfRuns := wf_of_runs
theorem RunsHeightsFromSource : Properties.RunsHeightsFromSource := @runs_heights_from_source
theorem WfOfHeightsFromSource : Properties.WfOfHeightsFromSource := wf_of_heights_from_source
theorem WfSourceHeightsFromRuns : Properties.WfSourceHeightsFromRuns := wf_source_heights_from_runs
theorem BeginHeightFromSource : Properties.BeginHeightFromSource := begin_height_from_source
theorem NoneOrAllOrBreakPinnedFromRuns : Properties.NoneOrAllOrBreakPinnedFromRuns :=
  none_or_all_or_break_pinned_from_runs
theorem PaddedSystemFromRuns : Properties.PaddedSystemFromRuns := padded_system_from_runs
theorem MixedSystemFromRuns : Properties.MixedSystemFromRuns := mixed_system_from_runs
theorem NoneOrAllOrBreakPinnedFromRunsStranded : Properties.NoneOrAllOrBreakPinnedFromRunsStranded :=
  none_or_all_or_break_pinned_from_runs_stranded

end Contracts.Atomicity
