import EraSpec.Contracts.AtomicInteropProof.Specs.StaleSnapshotBranches
import EraSpec.Contracts.AtomicInteropProof.Specs.LastBatchInRootOffset

/-!
# Properties: the stale-snapshot pin on the two deployed branches

Statements over `../Specs/StaleSnapshotBranches.lean`.  Proofs:
`../Proofs/StaleSnapshotBranches.lean`.

* `BeginBranchGivesPin` / `EndBranchGivesPin` — each deployed branch yields
  `StaleSnapshot`'s pin, at `j = L - 1` under `BeginIsPrevEnd`, and at `j = B` under
  `LaterBatchesLate B` (every batch numbered after `B` settles no earlier than the root).
* `BeginBranchNotRedeemable` / `EndBranchNotRedeemable` — `StaleSnapshot`'s headline,
  re-proved for the gate as deployed: a genuine witness accepted on either branch
  excludes every on-time delivery.  The end branch needs no timestamp monotonicity.
* `LaterBatchesLateOfOffset` / `OutsideRootLateGivesLaterBatchesLate` — where the
  end-branch bridge comes from: it is exactly `LastBatchInRootOffset`'s re-indexed premise
  at `B = batchAt f p`, `n = p + 1`; the unrestricted `OutsideRootLate` (false at the pin
  for EraVM chains) implies it, and is not used.
* `BeginBranchNeedsBeginIsPrevEnd` / `EndBranchNeedsLaterBatchesLate` — each bridging
  assumption is load-bearing: without it, a branch passes with a genuine witness for a
  value delivered on time.
* `PinBoundsOnTime` / `PinDoesNotMakeSnapshotOnTime` / `BeginBranchPinMayBeLate` —
  what `D < t (j+1)` means: every on-time snapshot is at or before `j`; `j` itself need
  not be on time (so "j is the LAST on-time snapshot" is wrong without `t j ≤ D`), and
  on the begin branch it can be late.
* `BeginBranchNotRedeemableSatisfiable` / `EndBranchNotRedeemableSatisfiable` — every
  premise of each headline holds together on an honest refund with an on-time batch, so
  neither headline is vacuous.  The end-branch witness is a fresh EraVM chain
  (`eraVMHonestHistory`, batch 0 never in a root), on which the unrestricted
  `OutsideRootLate` is false.
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

/-- **THE END BRANCH GIVES THE PIN, UNDER `LaterBatchesLate`.**  A witness in batch `B`'s
end snapshot, in a root created after the deadline, with every batch numbered after `B`
settling no earlier than the root, is a witness in snapshot `j = B` with `D < t (B+1)`. -/
def Properties.EndBranchGivesPin : Prop :=
  ∀ (H : BatchSnapshots) (D T v : UInt256) (B : ℕ) (W : AbsLeaf),
    LaterBatchesLate B H.t T → EndBranch H D T v B W →
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
a sound base, with `LaterBatchesLate B H.t T` (every batch numbered after `B` settles no
earlier than the root time `T`), a genuine end-branch witness at batch `B` for `v` means
`v` is a key of no on-time end snapshot.  No timestamp monotonicity is used, and batches
before `B` (including batches never pushed into any root) are unconstrained. -/
def Properties.EndBranchNotRedeemable : Prop :=
  ∀ (H : BatchSnapshots) (D T v : UInt256) (B : ℕ) (W : AbsLeaf),
    Evolution H.endS → SoundState (H.endS 0) → LaterBatchesLate B H.t T →
    EndBranch H D T v B W → ∀ i, H.t i ≤ D → v ∉ keys (H.endS i)

/-- **THE END-BRANCH BRIDGE IS `LastBatchInRootOffset`'S RE-INDEXED PREMISE.**  For a
chain tree whose first leaf is batch `f`, holding `n = p + 1` leaves with the proof at
position `p` (the last leaf, `last_of_rightEmpty`), "every batch `m ≥ f + n` settles no
earlier than `T`" (the premise of `EndBranchFromOnchainCheckOffset`) is exactly
`LaterBatchesLate (batchAt f p)`. -/
def Properties.LaterBatchesLateOfOffset : Prop :=
  ∀ (H : AttackVectors.TimeoutSoundness.BatchHistory) (f p T : ℕ),
    (∀ m, f + (p + 1) ≤ m → T ≤ H.time m) ↔
      LaterBatchesLate (AttackVectors.LastBatchInRootOffset.batchAt f p) H.time T

/-- **THE UNRESTRICTED FORM IMPLIES THE RESTRICTED ONE.**  If every batch outside the root
settles no earlier than `T` and every batch in the root is at most `B` (the index
reading of `_verifyLastBatchInRoot`), then `LaterBatchesLate B`.  The converse fails
(`EndBranchNotRedeemableSatisfiable`), and no headline here takes the unrestricted form. -/
def Properties.OutsideRootLateGivesLaterBatchesLate : Prop :=
  ∀ (inRoot : ℕ → Prop) (t : ℕ → UInt256) (T : UInt256) (B : ℕ),
    OutsideRootLate inRoot t T → (∀ m, inRoot m → m ≤ B) → LaterBatchesLate B t T

/-- **`BeginIsPrevEnd` IS LOAD-BEARING.**  `unlinkedHistory` has a sound evolution of end
snapshots and monotone timestamps but begin snapshots stuck at genesis; the begin branch
passes at batch 2 with the genesis leaf as a genuine member of the begin snapshot, while
`1` was committed in batch 0 and is in batch 1's end snapshot, on time. -/
def Properties.BeginBranchNeedsBeginIsPrevEnd : Prop :=
  Evolution unlinkedHistory.endS ∧ SoundState (unlinkedHistory.endS 0)
    ∧ Monotone unlinkedHistory.t ∧ ¬ BeginIsPrevEnd unlinkedHistory
    ∧ BeginBranch unlinkedHistory 0 1 1 2 ⟨0, 0⟩
    ∧ unlinkedHistory.t 1 ≤ 0 ∧ (1 : UInt256) ∈ keys (unlinkedHistory.endS 1)

/-- **`LaterBatchesLate` IS LOAD-BEARING.**  `staleRootHistory` satisfies `BeginIsPrevEnd`
and has monotone timestamps; a root created at time 1 whose last batch is batch 0 makes
the end branch pass at batch 0 with a genuine witness, while `1` is in batch 1's end
snapshot and batch 1 settled on time.  Batch 1 > 0 settled at time 0 < 1, so
`LaterBatchesLate 0` fails. -/
def Properties.EndBranchNeedsLaterBatchesLate : Prop :=
  Evolution staleRootHistory.endS ∧ SoundState (staleRootHistory.endS 0)
    ∧ Monotone staleRootHistory.t ∧ BeginIsPrevEnd staleRootHistory
    ∧ ¬ LaterBatchesLate 0 staleRootHistory.t 1
    ∧ EndBranch staleRootHistory 0 1 1 0 ⟨0, 0⟩
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

/-- **THE BEGIN-BRANCH PREMISES ARE SATISFIABLE.**  On `honestHistory` (nothing committed,
batch 0 on time for deadline `0`), the begin branch passes at batch `L = 1` with the
genesis leaf as witness for `v = 1`: every premise of `BeginBranchNotRedeemable` holds,
and batch 0 is on time, so its conclusion is not vacuous. -/
def Properties.BeginBranchNotRedeemableSatisfiable : Prop :=
  Evolution honestHistory.endS ∧ SoundState (honestHistory.endS 0) ∧ Monotone honestHistory.t
    ∧ BeginIsPrevEnd honestHistory ∧ BeginBranch honestHistory 0 1 1 1 ⟨0, 0⟩
    ∧ honestHistory.t 0 ≤ 0

/-- **THE END-BRANCH PREMISES ARE SATISFIABLE, ON A FRESH ERAVM CHAIN.**  On
`eraVMHonestHistory`, a root created at time 1 whose last batch is batch 1 (the chain's
first pushed batch, position 0) satisfies `LaterBatchesLate 1`, and the end branch passes
at batch `B = 1` (on time for deadline `0`) with the genesis leaf as witness for `v = 1`:
every premise of `EndBranchNotRedeemable` holds, and batch 1 is on time, so the
conclusion is not vacuous.  Batch 0 is in no root (`seedGenesisRoot` returns early for
EraVM chains) and settled at time 0, so the unrestricted `OutsideRootLate` with
`inRoot = (· = 1)` is false here. -/
def Properties.EndBranchNotRedeemableSatisfiable : Prop :=
  Evolution eraVMHonestHistory.endS ∧ SoundState (eraVMHonestHistory.endS 0)
    ∧ LaterBatchesLate 1 eraVMHonestHistory.t 1
    ∧ EndBranch eraVMHonestHistory 0 1 1 1 ⟨0, 0⟩
    ∧ ¬ OutsideRootLate (· = 1) eraVMHonestHistory.t 1

end AttackVectors.StaleSnapshotBranches
