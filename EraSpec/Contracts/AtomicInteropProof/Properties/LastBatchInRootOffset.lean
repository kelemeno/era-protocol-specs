import EraSpec.Contracts.AtomicInteropProof.Specs.LastBatchInRootOffset

/-!
# Properties: the end-branch composition with positions and batch numbers apart

Statements over `../Specs/LastBatchInRootOffset.lean`.  Proofs:
`../Proofs/LastBatchInRootOffset.lean`.

* `EndBranchFromOnchainCheckOffset` — `LastBatchInRoot.end_branch_from_onchain_check`
  re-indexed: the zero-cascade check on the mask POSITION `p`, the batch NUMBER
  `B = batchAt f p` (first pushed batch `f`), and `OutsideRootLate` only for batches
  after the root's last batch.  At `c67894b9` every atomic-interop source chain has
  `f = 0` on L1 (see the Specs); there `B = p`, the time premise is equivalent to the
  original `hout`, and the statement is the original one.  The offset form generalises
  it.
* `BatchNumberBoundOrCollision` — a definitional case split with no derived content:
  `B = batchAt f p`, or the two named preimages collide.  It takes no premise beyond the
  leaf equality; that the leaf at position `p` carries batch number `batchAt f p` at all
  is `PROTO-CONTIGUOUS-PUSH`.
* `PositionAsBatchMisreads` — on an abstract chain whose first pushed batch is 1, which
  no atomic-interop source chain has at `c67894b9`, the original statement's `hout` is
  false (and its conclusion, read with the position as the batch number, is false),
  while the re-indexed premise holds and the re-indexed absence correctly fails.
* `EndBranchOffsetSatisfiable` — every premise of the re-indexed form holds together on
  `richOffsetHistory` (again `f = 1`, three batches in the root).  `RightEmpty`, the index
  content of the zero-cascade check, fails for the same position once a fourth leaf
  exists, and a value is committed on time, so the headline separates that value from
  the refunded one; the original `hout` is again false there.
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

/-- **THE PROOF'S BATCH NUMBER IS THE STORED LEAF'S, OR TWO NAMED PREIMAGES COLLIDE.**  If
the proof's leaf `bl R B tB` (`batchLeafHash(batchSettlementRoot, batchNumber,
l1BatchTimestamp)`) equals the leaf stored at position `p`, `bl Rp (batchAt f p) tp`,
then `B = batchAt f p`, or those two distinct preimages collide.

This is a definitional case split with no derived content: it has no premise beyond the
leaf equality, its proof is a case split on `B = batchAt f p`, and its collision
disjunct restates that premise, so it says nothing about the hash `bl`.  It does not
show that the leaf stored at position `p` has batch number `batchAt f p`; that is the
assumption `PROTO-CONTIGUOUS-PUSH` (pushed batches are contiguous from `f`), which
`MessageRootBase` does not enforce. -/
def Properties.BatchNumberBoundOrCollision : Prop :=
  ∀ (bl : UInt256 → ℕ → ℕ → UInt256) (R Rp : UInt256) (B tB f p tp : ℕ),
    bl R B tB = bl Rp (batchAt f p) tp →
      B = batchAt f p ∨ ((R, B, tB) ≠ (Rp, batchAt f p, tp) ∧ bl R B tB = bl Rp (batchAt f p) tp)

/-- **THE POSITION-AS-BATCH READING FAILS WHEN THE FIRST PUSHED BATCH IS 1.**
`offsetHistory` is an abstract chain whose first pushed batch is batch 1 (`f = 1`): its
root holds one leaf, at position 0, which is batch 1.  Every premise of
`end_branch_from_onchain_check` with `B = 0`, `nBatches = 1`, `hDepth = 0`, `D = 0`,
`T = 1`, `v = 1` holds except `hout`, which is false (batch 1 is outside `{m | m < 1}` but
settled at time 0); its conclusion is false too (value `1` is in batch 1's end set, on
time).  The re-indexed `hout` holds, and the re-indexed absence premise (at batch
`batchAt 1 0 = 1`) is false, as it must be.

No atomic-interop source chain has `f > 0` at `c67894b9`: each is genesis-seeded with
batch 0 on L1, where the original reading is exact while pushes are contiguous.  So this
is the case the offset form generalises to, not a misreading of a chain the pinned end
branch serves; the name is kept for continuity. -/
def Properties.PositionAsBatchMisreads : Prop :=
  AppendOnly offsetHistory ∧ (0 : ℕ) < 1 ∧ (0 : ℕ) < 1 ∧ 1 ≤ 2 ^ 0 ∧ RightEmpty 0 1 0
    ∧ (1 : UInt256) ∉ offsetHistory.endSet 0
    ∧ ¬ OutsideRootLate (· < 1) offsetHistory.time 1
    ∧ ¬ (∀ B', offsetHistory.time B' ≤ 0 → (1 : UInt256) ∉ offsetHistory.endSet B')
    ∧ (∀ m, 1 + 1 ≤ m → 1 ≤ offsetHistory.time m)
    ∧ (1 : UInt256) ∈ offsetHistory.endSet (batchAt 1 0)

/-- **THE RE-INDEXED PREMISES ARE SATISFIABLE, AND THE HEADLINE DOES WORK.**  On
`richOffsetHistory`, read with first pushed batch `f = 1` (an abstract instance; no
atomic-interop source chain has `f > 0` at `c67894b9`): batches 1, 2 and 3 in the root
at positions 0, 1 and 2, the proof at position 2 (batch 3), root time `T = 1`, deadline
`D = 0`, value `v = 1`.  Every premise of `EndBranchFromOnchainCheckOffset` holds.
`RightEmpty` (the index content of the zero-cascade check) holds for position 2 of three
leaves and fails for position 2 of four, so the check is exercised.  Value `7` is
committed in batch 1, on time, so the headline's conclusion, which these premises give
for `1`, is false for `7`.  The original `hout` with `nBatches = 3` is false (batch 3 is
outside `{m | m < 3}` but settled at time 0). -/
def Properties.EndBranchOffsetSatisfiable : Prop :=
  AppendOnly richOffsetHistory ∧ (0 : ℕ) < 1 ∧ 3 = batchAt 1 2 ∧ 2 < 3
    ∧ 3 ≤ 2 ^ 2 ∧ RightEmpty 2 3 2
    ∧ (∀ m, 1 + 3 ≤ m → 1 ≤ richOffsetHistory.time m)
    ∧ (1 : UInt256) ∉ richOffsetHistory.endSet 3
    ∧ ¬ OutsideRootLate (· < 3) richOffsetHistory.time 1
    ∧ ¬ RightEmpty 2 4 2
    ∧ richOffsetHistory.time 1 ≤ 0 ∧ (7 : UInt256) ∈ richOffsetHistory.endSet 1

end AttackVectors.LastBatchInRootOffset
