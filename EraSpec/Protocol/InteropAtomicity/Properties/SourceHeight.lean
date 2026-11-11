import EraSpec.Protocol.InteropAtomicity.Specs.SourceHeight

/-!
# Properties: `Wf.capacity` derived from the runs

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.SourceHeight`; proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.SourceHeight`.

`Wf.capacity` is a premise of every atomicity, timeout and refund result.  For a system
built from contract runs that carry `FullMerkle._height`, it is a theorem
(`WfOfRuns`); and a `Wf` system whose heights are the source's is always so built
(`WfSourceHeightsFromRuns`), so nothing is lost by stating results this way.
-/

namespace Contracts.Atomicity

open IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree

/-- **`Wf` FROM THE RUNS.**  A system built from per-chain runs that carry their
`FullMerkle` dimensions is well formed; its `capacity` field is derived, not assumed. -/
def Properties.WfOfRuns : Prop :=
  ∀ (St : Chain → ℕ → HState) (time : Chain → ℕ → ℕ), RunsWf St time → Wf (systemOfRuns St time)

/-- The heights of such a system are the source's: `fmHeight` of the leaf count. -/
def Properties.RunsHeightsFromSource : Prop :=
  ∀ (St : Chain → ℕ → HState) (time : Chain → ℕ → ℕ), RunsWf St time →
    HeightsFromSource (systemOfRuns St time)

/-- **`Wf.capacity` FROM SOURCE HEIGHTS.**  The first three fields of `Wf` and source
heights give `Wf`. -/
def Properties.WfOfHeightsFromSource : Prop :=
  ∀ S : System, (∀ c, Reaches setup (S.tree c 0)) → (∀ c n, Reaches (S.tree c n) (S.tree c (n + 1)))
    → (∀ c, Monotone (S.time c)) → HeightsFromSource S → Wf S

/-- **NOTHING IS LOST.**  Every well-formed system with source heights is
`systemOfRuns` of some runs meeting `RunsWf`, with its own timestamps. -/
def Properties.WfSourceHeightsFromRuns : Prop :=
  ∀ S : System, Wf S → HeightsFromSource S →
    ∃ St : Chain → ℕ → HState, RunsWf St S.time ∧ systemOfRuns St S.time = S

/-- The BEGIN root's height is the source's too: `beginHeight` is `fmHeight` of
`beginTree`'s leaf count (at batch 0, `setup`'s one leaf and height `0`). -/
def Properties.BeginHeightFromSource : Prop :=
  ∀ S : System, HeightsFromSource S →
    ∀ c n, beginHeight S c n = fmHeight (beginTree S c n).leafCount

/-- **`NoneOrAllOrBreakPinned` FOR SYSTEMS BUILT FROM RUNS.**  The pinned partial
atomicity result with its `Wf` premise replaced by `RunsWf`, which has no capacity
field. -/
def Properties.NoneOrAllOrBreakPinnedFromRuns : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (St : Chain → ℕ → HState) (time : Chain → ℕ → ℕ), RunsWf St time →
    ∀ (A : Access), DataAvailable h z0 hl (systemOfRuns St time) A → ∀ (F : Flow) (ev : GateEvidence),
      FlowFinalizableBy h z0 hl cv (systemOfRuns St time) A F
        ∨ (∀ leg, ¬ ExecutedViaBy h z0 hl cv fh (systemOfRuns St time) F ev leg)
        ∨ PinnedGateBreak h z0 hl cv (systemOfRuns St time) A F ev

/-! ## Anti-vacuity -/

/-- **THE PADDING SYSTEM IS BUILT FROM RUNS.**  For `0 < a < b`, `paddedSystem a b`
(chain `0` at `threeLeafTree a b`, height 2) is `systemOfRuns` of runs meeting
`RunsWf`, with the batch numbers as timestamps.  So `RunsWf` is satisfiable with a
height that grew twice, and the height 2 the timeout and refund countermodels use is
the source's. -/
def Properties.PaddedSystemFromRuns : Prop :=
  ∀ a b : UInt256, 0 < a → a < b →
    ∃ St : Chain → ℕ → HState, RunsWf St (fun _ n => n)
      ∧ systemOfRuns St (fun _ n => n) = paddedSystem a b

/-- **THE MIXED SYSTEM IS BUILT FROM RUNS.**  For `0 < a`, `mixedSystem a` (chain `0` at
`insert setup a 0`, height 1) is `systemOfRuns` of runs meeting `RunsWf`. -/
def Properties.MixedSystemFromRuns : Prop :=
  ∀ a : UInt256, 0 < a →
    ∃ St : Chain → ℕ → HState, RunsWf St (fun _ n => n)
      ∧ systemOfRuns St (fun _ n => n) = mixedSystem a

/-- **`NoneOrAllOrBreakPinnedFromRuns`: PREMISES MET, BREAK EVALUATED ON A STRANDED LEG
AND FALSE.**  For every node hash, leaf hash and padding constant there are runs meeting
`RunsWf` whose system has, under honest access (which is data available), the flow
`mixedFlow 0 1 2` with first stranded leg `⟨1, 2⟩`, not all finalizable, and evidence
`ev` on which no leg executes and `PinnedGateBreak` is false. -/
def Properties.NoneOrAllOrBreakPinnedFromRunsStranded : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
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
              (honestAccess h z0 hl (systemOfRuns St (fun _ n => n))) (mixedFlow 0 1 2) ev

end Contracts.Atomicity
