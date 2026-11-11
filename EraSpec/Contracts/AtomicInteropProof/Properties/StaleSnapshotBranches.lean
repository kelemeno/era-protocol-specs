import EraSpec.Contracts.AtomicInteropProof.Specs.StaleSnapshotBranches

/-!
# Properties: the stale-snapshot pin on the two deployed branches

Statements over `../Specs/StaleSnapshotBranches.lean`.  Proofs:
`../Proofs/StaleSnapshotBranches.lean`.

* `BeginBranchGivesPin` / `EndBranchGivesPin` — each deployed branch yields
  `StaleSnapshot`'s pin, at `j = L - 1` under `BeginIsPrevEnd`, and at `j = B` under
  `OutsideRootLate`.
* `BeginBranchNotRedeemable` / `EndBranchNotRedeemable` — `StaleSnapshot`'s headline,
  re-proved for the gate as deployed: a genuine witness accepted on either branch
  excludes every on-time delivery.  The end branch needs no timestamp monotonicity.
* `BeginBranchNeedsBeginIsPrevEnd` / `EndBranchNeedsOutsideRootLate` — each bridging
  assumption is load-bearing: without it, a branch passes with a genuine witness for a
  value delivered on time.
* `PinBoundsOnTime` / `PinDoesNotMakeSnapshotOnTime` / `BeginBranchPinMayBeLate` —
  what `D < t (j+1)` means: every on-time snapshot is at or before `j`; `j` itself need
  not be on time (so "j is the LAST on-time snapshot" is wrong without `t j ≤ D`), and
  on the begin branch it can be late.
-/

namespace AttackVectors.StaleSnapshotBranches

open IMTAbstract

/-- **THE BEGIN BRANCH GIVES THE PIN, UNDER `BeginIsPrevEnd`.**  A witness in batch `L`'s
begin snapshot with batch `L` late is a witness in snapshot `j = L - 1` with
`D < t (j+1)`. -/
def Properties.BeginBranchGivesPin : Prop :=
  ∀ (H : BatchSnapshots) (D T v : UInt256) (L : ℕ) (W : AbsLeaf),
    BeginIsPrevEnd H → 0 < L → BeginBranch H D T v L W →
      W ∈ H.endS (L - 1) ∧ D < H.t (L - 1 + 1)

/-- **THE END BRANCH GIVES THE PIN, UNDER `OutsideRootLate`.**  A witness in batch `B`'s
end snapshot, with `B` the last batch in a root created after the deadline, is a witness
in snapshot `j = B` with `D < t (B+1)`. -/
def Properties.EndBranchGivesPin : Prop :=
  ∀ (H : BatchSnapshots) (inRoot : ℕ → Prop) (D T v : UInt256) (B : ℕ) (W : AbsLeaf),
    OutsideRootLate inRoot H.t T → EndBranch H inRoot D T v B W →
      W ∈ H.endS B ∧ D < H.t (B + 1)

/-- **`StaleSnapshot`'S HEADLINE ON THE DEPLOYED BEGIN BRANCH.**  Along an evolution
from a sound base, with monotone batch timestamps and `BeginIsPrevEnd`, a genuine
begin-branch witness for `v` means `v` is a key of no on-time end snapshot.  (For
`L = 0` this is monotonicity alone: no batch is on time.) -/
def Properties.BeginBranchNotRedeemable : Prop :=
  ∀ (H : BatchSnapshots) (D T v : UInt256) (L : ℕ) (W : AbsLeaf),
    Evolution H.endS → SoundState (H.endS 0) → Monotone H.t → BeginIsPrevEnd H →
    BeginBranch H D T v L W → ∀ i, H.t i ≤ D → v ∉ keys (H.endS i)

/-- **`StaleSnapshot`'S HEADLINE ON THE DEPLOYED END BRANCH.**  Along an evolution from
a sound base, with `OutsideRootLate`, a genuine end-branch witness for `v` means `v` is a
key of no on-time end snapshot.  No timestamp monotonicity is used. -/
def Properties.EndBranchNotRedeemable : Prop :=
  ∀ (H : BatchSnapshots) (inRoot : ℕ → Prop) (D T v : UInt256) (B : ℕ) (W : AbsLeaf),
    Evolution H.endS → SoundState (H.endS 0) → OutsideRootLate inRoot H.t T →
    EndBranch H inRoot D T v B W → ∀ i, H.t i ≤ D → v ∉ keys (H.endS i)

/-- **`BeginIsPrevEnd` IS LOAD-BEARING.**  `unlinkedHistory` has a sound evolution of end
snapshots and monotone timestamps but begin snapshots stuck at genesis; the begin branch
passes at batch 2 with the genesis leaf as a genuine member of the begin snapshot, while
`1` was committed in batch 0 and is in batch 1's end snapshot, on time. -/
def Properties.BeginBranchNeedsBeginIsPrevEnd : Prop :=
  Evolution unlinkedHistory.endS ∧ SoundState (unlinkedHistory.endS 0)
    ∧ Monotone unlinkedHistory.t ∧ ¬ BeginIsPrevEnd unlinkedHistory
    ∧ BeginBranch unlinkedHistory 0 1 1 2 ⟨0, 0⟩
    ∧ unlinkedHistory.t 1 ≤ 0 ∧ (1 : UInt256) ∈ keys (unlinkedHistory.endS 1)

/-- **`OutsideRootLate` IS LOAD-BEARING.**  `staleRootHistory` satisfies `BeginIsPrevEnd`
and has monotone timestamps; a root created at time 1 that holds only batch 0 makes the
end branch pass at batch 0 with a genuine witness, while `1` is in batch 1's end snapshot
and batch 1 settled on time.  The root violates `OutsideRootLate`. -/
def Properties.EndBranchNeedsOutsideRootLate : Prop :=
  Evolution staleRootHistory.endS ∧ SoundState (staleRootHistory.endS 0)
    ∧ Monotone staleRootHistory.t ∧ BeginIsPrevEnd staleRootHistory
    ∧ ¬ OutsideRootLate (· ≤ 0) staleRootHistory.t 1
    ∧ EndBranch staleRootHistory (· ≤ 0) 0 1 1 0 ⟨0, 0⟩
    ∧ staleRootHistory.t 1 ≤ 0 ∧ (1 : UInt256) ∈ keys (staleRootHistory.endS 1)

/-- **WHAT THE PIN SAYS.**  Under monotone timestamps, `D < t (j+1)` puts every on-time
snapshot at or before `j`. -/
def Properties.PinBoundsOnTime : Prop :=
  ∀ (t : ℕ → UInt256) (D : UInt256) (j : ℕ), Monotone t → D < t (j + 1) →
    ∀ i, t i ≤ D → i ≤ j

/-- **WHAT THE PIN DOES NOT SAY.**  `D < t (j+1)` with monotone `t` does not make `j`
on time, so it does not pin `j` as "the last on-time snapshot". -/
def Properties.PinDoesNotMakeSnapshotOnTime : Prop :=
  ∃ (t : ℕ → UInt256) (D : UInt256) (j : ℕ), Monotone t ∧ D < t (j + 1) ∧ D < t j

/-- **ON THE BEGIN BRANCH THE PINNED SNAPSHOT CAN BE LATE.**  A begin-branch pass at batch
`L = 1` under `BeginIsPrevEnd` whose pinned snapshot `j = L - 1 = 0` is itself late. -/
def Properties.BeginBranchPinMayBeLate : Prop :=
  ∃ (H : BatchSnapshots) (D T v : UInt256) (L : ℕ) (W : AbsLeaf),
    BeginIsPrevEnd H ∧ BeginBranch H D T v L W ∧ 0 < L ∧ D < H.t (L - 1)

end AttackVectors.StaleSnapshotBranches
