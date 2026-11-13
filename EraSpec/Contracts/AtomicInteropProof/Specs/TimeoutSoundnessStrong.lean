import Mathlib.Tactic

import EraSpec.Contracts.AtomicInteropProof.Specs.TimeoutSoundness
import EraSpec.Contracts.AtomicInteropProof.Specs.LastBatchInRoot

/-!
# Spec: the timeout gate, with the branch flag and the authenticated leaf kept apart

Source, in the pinned era-contracts tree (`c67894b9`):
`contracts/atomic-interop/libraries/AtomicInteropProof.sol`, `verifyTimeoutAbsence`.  The
prover declares the branch (`_absence.provesAgainstBeginRoot`), and the contract derives from
that one flag BOTH the chain-batch-root leaf it authenticates

    uint256 imtRootLeafIndex = _absence.provesAgainstBeginRoot
        ? ChainBatchRootTree.IMT_BEGIN_ROOT_LEAF_INDEX     // leaf 2: IMT root at batch begin
        : ChainBatchRootTree.IMT_END_ROOT_LEAF_INDEX;      // leaf 3: IMT root at batch end
    ... _authenticateRoot(_absence, imtRootLeafIndex) ...

AND the branch checks: the imported root must be created after the deadline
(`rootTimestamp > _deadline`); then the begin branch needs `l1BatchTimestamp > _deadline`, and
the end branch needs `l1BatchTimestamp <= _deadline` plus `_verifyLastBatchInRoot`.  Finally
the non-inclusion proof is checked against the authenticated root.

`TimeoutSoundness.end_branch_with_begin_root_unsound` is about what happens when the leaf is not
tied to the flag, but it drops the end branch's own checks.  To state that question with every
check in place, this file keeps the flag and the leaf as SEPARATE inputs of the gate
(`TimeoutGateAt`) and names the deployed coupling (`deployedLeaf`).

Statements: `../Properties/TimeoutSoundnessStrong.lean`.  Proofs:
`../Proofs/TimeoutSoundnessStrong.lean`.

Model boundaries are those of `TimeoutSoundness`: an abstract `BatchHistory`, and
`_verifyLastBatchInRoot` entering as its abstract content `hlast` (every batch after the proven
one settles no earlier than the root's creation time `T`).  The on-chain form of that check is
`LastBatchInRoot.RightEmpty` together with the aggregation assumption
`LastBatchInRoot.OutsideRootLate`.  Hashes, proof encodings, and the settlement-layer
chain-id check are not modelled.
-/

namespace AttackVectors.TimeoutSoundness


/-- The two IMT leaves of a chain batch root that a timeout proof can be authenticated against
(`ChainBatchRootTree.IMT_BEGIN_ROOT_LEAF_INDEX = 2`, `IMT_END_ROOT_LEAF_INDEX = 3`).  The
`bool` flag limits the choice to these two, so authentication never points at the logs or
multichain leaves. -/
inductive ImtRootLeaf
  /-- Leaf 2: the IMT root at the BEGIN of the batch. -/
  | beginRoot
  /-- Leaf 3: the IMT root at the END of the batch. -/
  | endRoot
  deriving DecidableEq


/-- The committed values that leaf `r` of batch `n`'s chain batch root commits to: the begin set
for leaf 2, the end set for leaf 3. -/
def ImtRootLeaf.contents (H : BatchHistory) : ImtRootLeaf → ℕ → Finset UInt256
  | .beginRoot => beginSet H
  | .endRoot => H.endSet


/-- **THE DEPLOYED COUPLING.**  `verifyTimeoutAbsence` derives the authenticated leaf from the
declared branch: `provesAgainstBeginRoot ? IMT_BEGIN_ROOT_LEAF_INDEX : IMT_END_ROOT_LEAF_INDEX`. -/
def deployedLeaf (provesAgainstBeginRoot : Bool) : ImtRootLeaf :=
  if provesAgainstBeginRoot then .beginRoot else .endRoot


/-- The leg FINALIZES, as the library header defines it: its commit value is in the batch-END
IMT root of some batch with `t ≤ deadline`.  `¬ FinalizedBy H D v` is the conclusion of every
soundness result in `TimeoutSoundness` (`∀ B, H.time B ≤ D → v ∉ H.endSet B`). -/
def FinalizedBy (H : BatchHistory) (D : ℕ) (v : UInt256) : Prop :=
  ∃ B, H.time B ≤ D ∧ v ∈ H.endSet B


/-- The checks the declared branch selects for the proven batch `n`, against a root created at
`T`.  Begin branch: the batch settled after the deadline (`l1BatchTimestamp > _deadline`).  End
branch: the batch settled by the deadline (`l1BatchTimestamp <= _deadline`), and every later
batch settles no earlier than `T` (`hlast`, the abstract content of `_verifyLastBatchInRoot`). -/
def TimeoutBranchChecks (H : BatchHistory) (D T : ℕ) : Bool → ℕ → Prop
  | true, n => D < H.time n
  | false, n => H.time n ≤ D ∧ ∀ m, n < m → T ≤ H.time m


/-- **`verifyTimeoutAbsence`, WITH THE FLAG AND THE LEAF AS SEPARATE INPUTS.**  The root was
created strictly after the deadline (`rootTimestamp > _deadline`), the declared branch's checks
pass for batch `n`, and `v` is absent from the contents of `leaf` of batch `n`.

The deployed gate is `TimeoutGateAt H D T b (deployedLeaf b) n v`.  The other two combinations,
`(true, endRoot)` and `(false, beginRoot)`, are the two root swaps. -/
def TimeoutGateAt (H : BatchHistory) (D T : ℕ) (provesAgainstBeginRoot : Bool)
    (leaf : ImtRootLeaf) (n : ℕ) (v : UInt256) : Prop :=
  D < T ∧ TimeoutBranchChecks H D T provesAgainstBeginRoot n ∧ v ∉ leaf.contents H n


/-- The countermodel history for the root swap.  Batch `0` is empty, value `0` is inserted
during batch `1`, and nothing is inserted afterwards.  Batches `0` and `1` settle at time `0`,
and every later batch at time `5`.  Settlement times are monotone, so the history is
`TimeOrdered` as well as append-only. -/
def rootSwapHistory : BatchHistory where
  endSet := fun n => if n = 0 then ∅ else {0}
  time := fun n => if n ≤ 1 then 0 else 5


/-- The history used by the proof of `end_branch_with_begin_root_unsound`.  It has the same END
sets as `rootSwapHistory`, but EVERY batch settles at time `0`.  No batch is ever late, so no
root created after a deadline can satisfy `hlast` on it. -/
def allInTimeHistory : BatchHistory where
  endSet := fun n => if n = 0 then ∅ else {0}
  time := fun _ => 0


end AttackVectors.TimeoutSoundness
