import EraSpec.Contracts.AtomicInteropProof.Specs.LastBatchInRootOffset

/-!
# Properties: the end-branch composition with positions and batch numbers apart

Statements over `../Specs/LastBatchInRootOffset.lean`.  Proofs:
`../Proofs/LastBatchInRootOffset.lean`.

* `EndBranchFromOnchainCheckOffset` — `LastBatchInRoot.end_branch_from_onchain_check`
  re-indexed: the zero-cascade check on the mask POSITION `p`, the batch NUMBER
  `B = batchAt f p` (first pushed batch `f`; `f = 0` for a genesis-seeded ZKsync OS
  chain), and `OutsideRootLate` only for batches after the root's last batch.
* `BatchNumberBoundOrCollision` — the pinned-collision restatement of "the leaf hash binds
  the batch number": `B = batchAt f p`, or the two named preimages collide.  It takes no
  premise beyond the leaf equality and is a case split; that the leaf at position `p`
  carries batch number `batchAt f p` at all is `PROTO-CONTIGUOUS-PUSH`.
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
chain `c`'s batches `f .. f + n - 1` at positions `0 .. n - 1` (`PROTO-CONTIGUOUS-PUSH`;
the statement takes `B = batchAt f p` as a premise).  If the zero-cascade
check passes for position `p` (`RightEmpty p n hDepth`), the proven batch is
`B = batchAt f p`, every batch after the root's last batch `f + n - 1` (every `m ≥ f + n`)
settles no earlier than the root time `T > D`, and the value is absent from `B`'s end set, then it is
absent from the end set of every on-time batch. -/
def Properties.EndBranchFromOnchainCheckOffset : Prop :=
  ∀ (H : BatchHistory) (f n p hDepth B D T : ℕ) (v : UInt256),
    AppendOnly H → D < T → B = batchAt f p →
    p < n → n ≤ 2 ^ hDepth → RightEmpty p n hDepth →
    (∀ m, f + n ≤ m → T ≤ H.time m) →
    v ∉ H.endSet B →
      ∀ B', H.time B' ≤ D → v ∉ H.endSet B'

/-- **THE BATCH NUMBER IS BOUND BY THE LEAF HASH, OR TWO NAMED PREIMAGES COLLIDE.**  If
the proof's leaf `bl R B tB` (`batchLeafHash(batchSettlementRoot, batchNumber,
l1BatchTimestamp)`) equals the leaf stored at position `p`, `bl Rp (batchAt f p) tp`,
then `B = batchAt f p`, or those two distinct preimages collide.

This is the pinned-collision restatement only: it has no premise beyond the leaf
equality, and its proof is a case split on `B = batchAt f p`.  It does not show that the
leaf stored at position `p` has batch number `batchAt f p`; that is the assumption
`PROTO-CONTIGUOUS-PUSH` (pushed batches are contiguous from `f`), which `MessageRootBase`
does not enforce. -/
def Properties.BatchNumberBoundOrCollision : Prop :=
  ∀ (bl : UInt256 → ℕ → ℕ → UInt256) (R Rp : UInt256) (B tB f p tp : ℕ),
    bl R B tB = bl Rp (batchAt f p) tp →
      B = batchAt f p ∨ ((R, B, tB) ≠ (Rp, batchAt f p, tp) ∧ bl R B tB = bl Rp (batchAt f p) tp)

/-- **THE POSITION-AS-BATCH READING FAILS ON A FRESH ERAVM CHAIN.**  `offsetHistory` is a
fresh EraVM chain: its root holds one leaf, at position 0, which is batch 1.  Every
premise of `end_branch_from_onchain_check` with `B = 0`, `nBatches = 1`, `hDepth = 0`,
`D = 0`, `T = 1`, `v = 1` holds except `hout`, which is false (batch 1 is outside
`{m | m < 1}` but settled at time 0); its conclusion is false too (value `1` is in batch
1's end set, on time).  The re-indexed `hout` holds, and the re-indexed absence premise
(at batch `batchAt 1 0 = 1`, first pushed batch `f = 1`) is false, as it must be. -/
def Properties.PositionAsBatchMisreads : Prop :=
  AppendOnly offsetHistory ∧ (0 : ℕ) < 1 ∧ (0 : ℕ) < 1 ∧ 1 ≤ 2 ^ 0 ∧ RightEmpty 0 1 0
    ∧ (1 : UInt256) ∉ offsetHistory.endSet 0
    ∧ ¬ OutsideRootLate (· < 1) offsetHistory.time 1
    ∧ ¬ (∀ B', offsetHistory.time B' ≤ 0 → (1 : UInt256) ∉ offsetHistory.endSet B')
    ∧ (∀ m, 1 + 1 ≤ m → 1 ≤ offsetHistory.time m)
    ∧ (1 : UInt256) ∈ offsetHistory.endSet (batchAt 1 0)

/-- **THE RE-INDEXED PREMISES ARE SATISFIABLE.**  A fresh EraVM chain with batches 1 and 2
in the root at positions 0 and 1 (`f = 1`), nothing committed, the proof at position 1
(batch 2):
every premise of `EndBranchFromOnchainCheckOffset` holds, while the original `hout` with
`nBatches = 2` is false. -/
def Properties.EndBranchOffsetSatisfiable : Prop :=
  AppendOnly emptyOffsetHistory ∧ (0 : ℕ) < 1 ∧ 2 = batchAt 1 1 ∧ 1 < 2
    ∧ 2 ≤ 2 ^ 1 ∧ RightEmpty 1 2 1
    ∧ (∀ m, 1 + 2 ≤ m → 1 ≤ emptyOffsetHistory.time m)
    ∧ (1 : UInt256) ∉ emptyOffsetHistory.endSet 2
    ∧ ¬ OutsideRootLate (· < 2) emptyOffsetHistory.time 1

end AttackVectors.LastBatchInRootOffset
