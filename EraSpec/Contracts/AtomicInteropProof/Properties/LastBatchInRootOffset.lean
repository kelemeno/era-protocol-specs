import EraSpec.Contracts.AtomicInteropProof.Specs.LastBatchInRootOffset

/-!
# Properties: the end-branch composition with positions and batch numbers apart

Statements over `../Specs/LastBatchInRootOffset.lean`.  Proofs:
`../Proofs/LastBatchInRootOffset.lean`.

* `EndBranchFromOnchainCheckOffset` — `LastBatchInRoot.end_branch_from_onchain_check`
  re-indexed: the zero-cascade check on the mask POSITION `p`, the batch NUMBER
  `B = batchAt s p`, and `OutsideRootLate` only for batches after the root's last batch.
* `BatchNumberBoundOrCollision` — the identification `B = batchAt s p` is what the batch
  leaf hash binds, or a collision between two named preimages.
* `PositionAsBatchMisreads` — on a fresh EraVM chain the original statement's `hout` is
  false (and its conclusion, read with the position as the batch number, is false),
  while the re-indexed premise holds and the re-indexed absence correctly fails.
* `EndBranchOffsetSatisfiable` — every premise of the re-indexed form holds on an
  honest refund of a fresh EraVM chain with two batches in the root, where the
  original `hout` is again false.
-/

namespace AttackVectors.LastBatchInRootOffset

open AttackVectors.TimeoutSoundness AttackVectors.LastBatchInRoot

/-- **THE END-BRANCH CHAIN, WITH POSITIONS AND BATCH NUMBERS APART.**  The root holds
chain `c`'s batches `s + 1 .. s + n` at positions `0 .. n - 1`.  If the zero-cascade
check passes for position `p` (`RightEmpty p n hDepth`), the proven batch is
`B = batchAt s p`, every batch after the root's last batch `s + n` settles no earlier
than the root time `T > D`, and the value is absent from `B`'s end set, then it is
absent from the end set of every on-time batch. -/
def Properties.EndBranchFromOnchainCheckOffset : Prop :=
  ∀ (H : BatchHistory) (s n p hDepth B D T : ℕ) (v : UInt256),
    AppendOnly H → D < T → B = batchAt s p →
    p < n → n ≤ 2 ^ hDepth → RightEmpty p n hDepth →
    (∀ m, s + n < m → T ≤ H.time m) →
    v ∉ H.endSet B →
      ∀ B', H.time B' ≤ D → v ∉ H.endSet B'

/-- **THE BATCH NUMBER IS BOUND BY THE LEAF HASH, OR TWO NAMED PREIMAGES COLLIDE.**  If
the proof's leaf `bl R B tB` (`batchLeafHash(batchSettlementRoot, batchNumber,
l1BatchTimestamp)`) equals the leaf stored at position `p`, `bl Rp (batchAt s p) tp`,
then `B = batchAt s p`, or those two distinct preimages collide. -/
def Properties.BatchNumberBoundOrCollision : Prop :=
  ∀ (bl : UInt256 → ℕ → ℕ → UInt256) (R Rp : UInt256) (B tB s p tp : ℕ),
    bl R B tB = bl Rp (batchAt s p) tp →
      B = batchAt s p ∨ ((R, B, tB) ≠ (Rp, batchAt s p, tp) ∧ bl R B tB = bl Rp (batchAt s p) tp)

/-- **THE POSITION-AS-BATCH READING FAILS ON A FRESH ERAVM CHAIN.**  `offsetHistory` is a
fresh EraVM chain: its root holds one leaf, at position 0, which is batch 1.  Every
premise of `end_branch_from_onchain_check` with `B = 0`, `nBatches = 1`, `hDepth = 0`,
`D = 0`, `T = 1`, `v = 1` holds except `hout`, which is false (batch 1 is outside
`{m | m < 1}` but settled at time 0); its conclusion is false too (value `1` is in batch
1's end set, on time).  The re-indexed `hout` holds, and the re-indexed absence premise
(at batch `batchAt 0 0 = 1`) is false, as it must be. -/
def Properties.PositionAsBatchMisreads : Prop :=
  AppendOnly offsetHistory ∧ (0 : ℕ) < 1 ∧ (0 : ℕ) < 1 ∧ 1 ≤ 2 ^ 0 ∧ RightEmpty 0 1 0
    ∧ (1 : UInt256) ∉ offsetHistory.endSet 0
    ∧ ¬ OutsideRootLate (· < 1) offsetHistory.time 1
    ∧ ¬ (∀ B', offsetHistory.time B' ≤ 0 → (1 : UInt256) ∉ offsetHistory.endSet B')
    ∧ (∀ m, 0 + 1 < m → 1 ≤ offsetHistory.time m)
    ∧ (1 : UInt256) ∈ offsetHistory.endSet (batchAt 0 0)

/-- **THE RE-INDEXED PREMISES ARE SATISFIABLE.**  A fresh EraVM chain with batches 1 and 2
in the root at positions 0 and 1, nothing committed, the proof at position 1 (batch 2):
every premise of `EndBranchFromOnchainCheckOffset` holds, while the original `hout` with
`nBatches = 2` is false. -/
def Properties.EndBranchOffsetSatisfiable : Prop :=
  AppendOnly emptyOffsetHistory ∧ (0 : ℕ) < 1 ∧ 2 = batchAt 0 1 ∧ 1 < 2
    ∧ 2 ≤ 2 ^ 1 ∧ RightEmpty 1 2 1
    ∧ (∀ m, 0 + 2 < m → 1 ≤ emptyOffsetHistory.time m)
    ∧ (1 : UInt256) ∉ emptyOffsetHistory.endSet 2
    ∧ ¬ OutsideRootLate (· < 2) emptyOffsetHistory.time 1

end AttackVectors.LastBatchInRootOffset
