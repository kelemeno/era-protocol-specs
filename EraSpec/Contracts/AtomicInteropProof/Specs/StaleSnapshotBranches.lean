import EraSpec.Contracts.IndexedMerkleTree.Specs.Model

/-!
# The stale-snapshot pin, mapped onto the two deployed timeout branches

`AttackVectors.StaleSnapshot` and `AttackVectors.Timestamps` model the reclaim gate as
"a witness at snapshot `j`, pinned by `D < t (j+1)`", and say the pin makes `j` "the
LAST on-time snapshot".  The deployed gate has no such comparison.
`AtomicInteropProof.verifyTimeoutAbsence` (`AtomicInteropProof.sol:162-196`, pinned
`c67894b9`) has two branches, and neither reads a successor batch's timestamp:

* **begin** (`_absence.provesAgainstBeginRoot`): the absence proof is against leaf 2
  (the IMT root at the BEGIN of batch `L`), `l1BatchTimestamp > _deadline` is required
  (`:185-188`);
* **end**: the proof is against leaf 3 (the IMT root at the END of batch `B`),
  `l1BatchTimestamp <= _deadline` is required (`:189-192`) and `_verifyLastBatchInRoot`
  must pass (`:195`);
* both: the imported settlement-layer root must have `rootTimestamp > _deadline`
  (`:171-179`).

Each branch reaches the abstract pin only through an assumption nothing on chain
checks:

* begin: the witness sits in `begin(L)`, which is snapshot `L - 1` only if
  `begin(L) = end(L-1)` (`BeginIsPrevEnd`, the bootloader's batch-boundary snapshot;
  `AttackVectors.TimeoutSoundness.BeginIsPrevEnd`).  Then `j = L - 1` and the late batch
  `L = j + 1` gives `D < t (j+1)`.
* end: `j = B`, and `D < t (B+1)` holds only via `LaterBatchesLate B t T`, "every batch
  NUMBERED after `B` settles no earlier than `T`".  `_verifyLastBatchInRoot` gives only
  an INDEX fact (the proven leaf is the last leaf of the chain's tree in the root);
  `LaterBatchesLate` is the TIME fact the branch needs.  It is the restricted form
  `LastBatchInRootOffset` derives (`LaterBatchesLateOfOffset`).  The unrestricted
  `OutsideRootLate inRoot t T` ("every batch NOT in the root settles no earlier than
  `T`", `AttackVectors.LastBatchInRoot.hlast_of_last_in_root`) is false at the pin for
  every EraVM chain: `seedGenesisRoot` returns early for EraVM chains and
  `_addNewChain` starts an empty tree at `_startingBatchNumber`, so batch 0 (and batches
  `1 .. s` of a chain onboarded at `s > 0`) are in no root yet settle before `T`.  It is
  kept below only to state that it implies the restricted form.

And `D < t (j+1)` does not make `j` on time: in the begin branch `j = L - 1` may itself
be late.  What the pin does give, under monotone `t`, is that every on-time snapshot is
at or before `j`.

Witnesses here are genuine leaves (`W ∈ beginS L`, `W ∈ endS B`), as in
`StaleSnapshot`; the deployed verifier's acceptance of a padding slot is the subject of
`AttackVectors.StaleSnapshotFaithful`.

**This file is definitions only.**  Results: `../Properties/StaleSnapshotBranches.lean`.
-/

namespace AttackVectors.StaleSnapshotBranches

open IMTAbstract

/-- A source chain's IMT history at batch granularity: the IMT at the END of each batch
(leaf 3 of its chain batch root), the IMT at its BEGIN (leaf 2), recorded independently,
and each batch's `l1BatchTimestamp`. -/
structure BatchSnapshots where
  endS : ℕ → Finset AbsLeaf
  beginS : ℕ → Finset AbsLeaf
  t : ℕ → UInt256

/-- `begin(n+1) = end(n)`: a property of how the source chain snapshots its tree at batch
boundaries.  No on-chain check establishes it: `_authenticateRoot` authenticates one
IMT-root leaf (2 or 3) of ONE batch and never relates two batches. -/
def BeginIsPrevEnd (H : BatchSnapshots) : Prop :=
  ∀ n, H.beginS (n + 1) = H.endS n

/-- **UNRESTRICTED, FALSE AT THE PIN FOR ERAVM CHAINS.**  A batch outside the aggregated
root settles no earlier than the root's creation time `T` (`LastBatchInRoot.OutsideRootLate`,
on the `UInt256` clock `StaleSnapshot` uses).  Batches below a chain's first pushed batch
are never in any root but settle earlier, so this fails for every EraVM chain (batch 0)
and every chain onboarded at a non-zero starting batch.  No headline here takes it; see
`LaterBatchesLate`. -/
def OutsideRootLate (inRoot : ℕ → Prop) (t : ℕ → UInt256) (T : UInt256) : Prop :=
  ∀ n, ¬ inRoot n → T ≤ t n

/-- **THE END-BRANCH BRIDGE.**  Every batch numbered after `B` settles no earlier than the
root's creation time `T`.  This is the restricted form: batches before `B` (including
those never pushed) are unconstrained.  Generic in the clock type so that it also reads
over `TimeoutSoundness.BatchHistory.time`. -/
def LaterBatchesLate {α : Type} [LE α] (B : ℕ) (t : ℕ → α) (T : α) : Prop :=
  ∀ m, B < m → T ≤ t m

/-- `W`'s window straddles `v`: the shape `verifyNonInclusion` checks. -/
abbrev Straddles (W : AbsLeaf) (v : UInt256) : Prop :=
  W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)

/-- **THE BEGIN BRANCH, AS DEPLOYED** (with a genuine witness): the settlement-layer root
post-dates the deadline, batch `L` settled after it, and a leaf of batch `L`'s BEGIN
snapshot straddles `v`. -/
structure BeginBranch (H : BatchSnapshots) (D T v : UInt256) (L : ℕ) (W : AbsLeaf) : Prop where
  /-- `ProofInteropRootNotAfterDeadline`. -/
  rootLate : D < T
  /-- `ProofTimeoutBranchMismatch(true, …)`. -/
  late : D < H.t L
  mem : W ∈ H.beginS L
  window : Straddles W v

/-- **THE END BRANCH, AS DEPLOYED** (with a genuine witness): the root post-dates the
deadline, batch `B` settled by it, and a leaf of batch `B`'s END snapshot straddles `v`.
`_verifyLastBatchInRoot`'s index conclusion is not a field: what the branch uses from it
is the time fact `LaterBatchesLate B H.t T`, taken as a separate premise. -/
structure EndBranch (H : BatchSnapshots) (D T v : UInt256) (B : ℕ) (W : AbsLeaf) : Prop where
  /-- `ProofInteropRootNotAfterDeadline`. -/
  rootLate : D < T
  /-- `ProofTimeoutBranchMismatch(false, …)`. -/
  onTime : H.t B ≤ D
  mem : W ∈ H.endS B
  window : Straddles W v

/-! ## Countermodel histories -/

/-- Begin snapshots unrelated to end snapshots: every begin snapshot is the genesis
singleton, while the end snapshots of `Timestamps.attackHistory 1` commit `1` in batch 0.
Batches 0 and 1 settle at time 0, later ones at time 1. -/
def unlinkedHistory : BatchSnapshots where
  endS := fun m => if m = 0 then {⟨0, 0⟩} else imtInsert {⟨0, 0⟩} ⟨0, 0⟩ 1
  beginS := fun _ => {⟨0, 0⟩}
  t := fun n => if n ≤ 1 then 0 else 1

/-- A stale root: only batch 0 is in it, but batch 1 (which commits `1`) also settles by
the deadline. -/
def staleRootHistory : BatchSnapshots where
  endS := fun m => if m = 0 then {⟨0, 0⟩} else imtInsert {⟨0, 0⟩} ⟨0, 0⟩ 1
  beginS := fun m => if m ≤ 1 then {⟨0, 0⟩} else imtInsert {⟨0, 0⟩} ⟨0, 0⟩ 1
  t := fun _ => 0

/-- An honest refund on a fresh EraVM chain: nothing is ever committed (every snapshot is
the genesis singleton).  Batch 0 is never pushed (`seedGenesisRoot` returns early), batch
1 is the first pushed batch; batches 0 and 1 settle at time 0, later ones at time 1. -/
def eraVMHonestHistory : BatchSnapshots where
  endS := fun _ => {⟨0, 0⟩}
  beginS := fun _ => {⟨0, 0⟩}
  t := fun n => if n ≤ 1 then 0 else 1

/-- An honest refund history: nothing is ever committed (every snapshot is the genesis
singleton, begin and end alike), batch 0 settles at time 0 and every later batch at time 1. -/
def honestHistory : BatchSnapshots where
  endS := fun _ => {⟨0, 0⟩}
  beginS := fun _ => {⟨0, 0⟩}
  t := fun n => if n = 0 then 0 else 1

end AttackVectors.StaleSnapshotBranches
