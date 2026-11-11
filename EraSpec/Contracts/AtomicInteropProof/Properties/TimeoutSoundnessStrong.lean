import EraSpec.Contracts.AtomicInteropProof.Specs.TimeoutSoundnessStrong

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false


/-!
# The dangerous root swap, with every end-branch premise in place

`TimeoutSoundness.end_branch_with_begin_root_unsound` is meant to show that offering a BEGIN root
on the END branch is unsound, so the `_leafProofMask` binding in `verifyTimeoutAbsence` is
load-bearing.  As stated it is `∃ H D v B, AppendOnly H ∧ H.time B ≤ D ∧ v ∉ beginSet H B ∧
v ∈ H.endSet B`: some in-time batch inserted `v`.  It omits the end branch's own premises.  The
imported root must be created at `T > D`, and every batch after `B` must settle no earlier than
`T` (`hlast`, the abstract content of `_verifyLastBatchInRoot`).  Its witness settles every
batch at time `0`, so `hlast` holds for no `T > D`.  On that history, dropping `hlast` makes the
end branch unsound even with the CORRECT end root: batch `0`'s end set lacks the value, and the
in-time batch `1` contains it.  So the witness does not single out the root as the cause.

This file states the swap with every end-branch check in place, and then says exactly how much
the leaf binding buys:

* `end_branch_begin_root_admits_finalized`: the original existential plus `D < T`, `hlast` and
  `TimeOrdered`.
* `end_branch_begin_root_passes_onchain_checks`: the same, with `hlast` replaced by its on-chain
  form, the premise list of `LastBatchInRoot.end_branch_from_onchain_check`
  (`RightEmpty`, `OutsideRootLate`), and the contract's in-time check as well.
* `end_branch_needs_hlast` and `allInTimeHistory_no_hlast`: the other guard.  With the correct
  root but without `hlast` the end branch is unsound, and on the history the original proof uses
  `hlast` never holds.  So that witness shows a missing `hlast`, not a swapped root.
* `timeoutGate_end_flag_begin_leaf_admits_finalized`: the gate-level form.  The swapped gate
  accepts a finalized value that the deployed gate rejects on the same proof.
* `timeoutGate_end_flag_begin_leaf_iff_batch_insertion`: on every append-only history, the
  swapped gate is wrong EXACTLY on the values inserted during the proven batch.  Its witness
  `timeoutGate_end_flag_begin_leaf_iff_witness` has the swapped gate accept the same batch for a
  finalized value and for a value that never finalized.
* `timeoutGate_deployed_leaf_sound` and its witness `timeoutGate_deployed_leaf_not_dead`: the
  deployed coupling is sound on both branches, and both branches do open.
* `timeoutGate_sound_iff_not_end_flag_begin_leaf`: of the four (flag, leaf) combinations,
  exactly one is unsound over append-only, time-ordered histories, namely the end flag with
  the begin leaf.

No hash premise appears anywhere in this file.
-/

namespace AttackVectors.TimeoutSoundness


/-! ## The swap with every end-branch premise -/

/-- **THE DANGEROUS SWAP, WITH EVERY END-BRANCH PREMISE.**  There is an append-only,
time-ordered history, a deadline `D`, a root time `T` and an in-time batch `B` such that every
premise of `end_absence_implies_never_finalized` except the root's role holds: `H.time B ≤ D`,
`D < T`, and `hlast`.  The value is absent from `B`'s BEGIN set, yet `B` is in time and its END
set contains the value, so the leg finalized.

Compared with `end_branch_with_begin_root_unsound`, this adds `D < T`, `hlast` and
`TimeOrdered`.  `end_absence_implies_never_finalized` shows that with these premises the
correct end root IS sound, so here the begin root is the only thing that goes wrong.  The last
conjunct is also exactly why the correct root rejects the same proof. -/
abbrev Properties.end_branch_begin_root_admits_finalized :=
  ∃ (H : BatchHistory) (D T : ℕ) (v : UInt256) (B : ℕ),
    AppendOnly H ∧ TimeOrdered H ∧
      H.time B ≤ D ∧ D < T ∧ (∀ n, B < n → T ≤ H.time n) ∧
      v ∉ beginSet H B ∧ v ∈ H.endSet B


/-- **THE SWAP PASSES THE END BRANCH'S ON-CHAIN CHECKS.**  This is the countermodel against the
on-chain form of the end branch.  It uses the premise list of
`LastBatchInRoot.end_branch_from_onchain_check` (root after the deadline, `B` inside a root of
`nBatches` leaves fitting `hDepth` levels, the zero-cascade check `RightEmpty`, and the
aggregation assumption `OutsideRootLate`), plus the contract's own in-time check
`H.time B ≤ D`.  The absence is taken against `B`'s BEGIN set instead of its END set.  Every
check passes, and the value is in `B`'s END set: a finalized leg the swapped branch would refund.

So none of the end branch's time and position checks catches the swap.  Only the leaf index
the root is authenticated at does. -/
abbrev Properties.end_branch_begin_root_passes_onchain_checks :=
  ∃ (H : BatchHistory) (B nBatches hDepth D T : ℕ) (v : UInt256),
    AppendOnly H ∧ TimeOrdered H ∧
      D < T ∧ H.time B ≤ D ∧
      B < nBatches ∧ nBatches ≤ 2 ^ hDepth ∧
      LastBatchInRoot.RightEmpty B nBatches hDepth ∧
      LastBatchInRoot.OutsideRootLate (· < nBatches) H.time T ∧
      v ∉ beginSet H B ∧ v ∈ H.endSet B


/-! ## Why the original witness does not isolate the swap

The end branch has two guards beyond the time checks: the last-batch check (`hlast`) and the leaf
binding.  Each one is load-bearing on its own.  The countermodels above keep `hlast` and break
the leaf.  The one below keeps the leaf and drops `hlast`.  The history that the proof of
`end_branch_with_begin_root_unsound` uses is of the second kind. -/

/-- **THE LAST-BATCH CHECK IS LOAD-BEARING TOO.**  Drop `hlast` and the end branch is unsound even
with the CORRECT end root, on the very history `end_branch_with_begin_root_unsound` is proved on.
`allInTimeHistory` is append-only and time-ordered.  For some root time `T > D`, an in-time batch
`B` has an END set that lacks the value, yet the value finalized by the deadline in another batch.

This is the abstract counterpart of
`Applications.BurnMintBridge.EndBranch.UncheckedEndDoublePays`. -/
abbrev Properties.end_branch_needs_hlast :=
  AppendOnly allInTimeHistory ∧ TimeOrdered allInTimeHistory ∧
    ∃ (D T : ℕ) (v : UInt256) (B : ℕ),
      allInTimeHistory.time B ≤ D ∧ D < T ∧ v ∉ allInTimeHistory.endSet B ∧
        FinalizedBy allInTimeHistory D v


/-- **ON THE ORIGINAL WITNESS, `hlast` NEVER HOLDS.**  On `allInTimeHistory`, no batch `B`,
deadline `D` and root time `T > D` satisfy `hlast`.  So that history cannot exhibit the end branch
with all of its premises, whichever root is offered. -/
abbrev Properties.allInTimeHistory_no_hlast :=
  ∀ B D T : ℕ, D < T → ¬ ∀ n, B < n → T ≤ allInTimeHistory.time n


/-! ## The gate-level statements -/

/-- **THE SWAPPED GATE ACCEPTS A FINALIZED LEG THAT THE DEPLOYED GATE REJECTS.**  On an
append-only, time-ordered history, the gate with the END-branch flag and the BEGIN leaf accepts
batch `n` for a value that finalized by the deadline.  The deployed gate, whose leaf for the
end flag is the END leaf, rejects the same `(D, T, n, v)`.  The two gates differ only in the
leaf, so the leaf binding is what separates them. -/
abbrev Properties.timeoutGate_end_flag_begin_leaf_admits_finalized :=
  ∃ (H : BatchHistory) (D T n : ℕ) (v : UInt256),
    AppendOnly H ∧ TimeOrdered H ∧
      TimeoutGateAt H D T false .beginRoot n v ∧ FinalizedBy H D v ∧
      ¬ TimeoutGateAt H D T false (deployedLeaf false) n v


/-- **THE SWAP IS WRONG EXACTLY ON THE PROVEN BATCH'S OWN INSERTIONS.**  On every append-only
history, the swapped gate (END flag, BEGIN leaf) accepts a value that in fact finalized iff the
end-branch checks pass and the value is in `endSet n \ beginSet n`, i.e. it was inserted DURING
the proven batch.  A value already present at the batch's begin is rejected, and a value never
inserted by the batch's end did not finalize (`hlast` forces every in-time batch to be at or
before `n`).  So the damage is exactly one batch's insertions.

Witness for its premise, with both sides of the iff exercised:
`timeoutGate_end_flag_begin_leaf_iff_witness`. -/
abbrev Properties.timeoutGate_end_flag_begin_leaf_iff_batch_insertion {H : BatchHistory}
    (hao : AppendOnly H) (D T n : ℕ) (v : UInt256) :=
  (TimeoutGateAt H D T false .beginRoot n v ∧ FinalizedBy H D v) ↔
    (D < T ∧ TimeoutBranchChecks H D T false n ∧ v ∈ H.endSet n \ beginSet H n)


/-- **THE SWAPPED GATE'S VERDICT DOES NOT DETERMINE FINALIZATION.**  On one append-only,
time-ordered history, the swapped gate (END flag, BEGIN leaf) accepts the SAME batch `n` for
two values: one that finalized by the deadline and one that did not.  This witnesses the
premise of `timeoutGate_end_flag_begin_leaf_iff_batch_insertion` with its left-hand side true
for one value and false for the other. -/
abbrev Properties.timeoutGate_end_flag_begin_leaf_iff_witness :=
  ∃ (H : BatchHistory) (D T n : ℕ) (v w : UInt256),
    AppendOnly H ∧ TimeOrdered H ∧
      TimeoutGateAt H D T false .beginRoot n v ∧ FinalizedBy H D v ∧
      TimeoutGateAt H D T false .beginRoot n w ∧ ¬ FinalizedBy H D w


/-- **THE DEPLOYED COUPLING IS SOUND ON BOTH BRANCHES.**  On an append-only, time-ordered
history, if the gate accepts with the leaf derived from the flag (`deployedLeaf`), the value
did not finalize by the deadline.  This is `timeout_implies_never_finalized` restated over the
gate.  Witness for its premises: `timeoutGate_deployed_leaf_not_dead`. -/
abbrev Properties.timeoutGate_deployed_leaf_sound {H : BatchHistory}
    (hao : AppendOnly H) (hto : TimeOrdered H) {D T n : ℕ} {b : Bool} {v : UInt256}
    (hacc : TimeoutGateAt H D T b (deployedLeaf b) n v) :=
  ¬ FinalizedBy H D v


/-- **ANTI-VACUITY: THE DEPLOYED GATE OPENS ON BOTH BRANCHES.**  There is an append-only,
time-ordered history and a value that never finalized by `D` for which the deployed gate
accepts a begin-branch proof (against a late batch) AND an end-branch proof (against the last
in-time batch).  On the same history and deadline, another value did finalize.  So
`timeoutGate_deployed_leaf_sound` is not explained by a gate that never fires, or by a history
in which nothing commits. -/
abbrev Properties.timeoutGate_deployed_leaf_not_dead :=
  ∃ (H : BatchHistory) (D T : ℕ) (v w : UInt256),
    AppendOnly H ∧ TimeOrdered H ∧
      (∃ L, TimeoutGateAt H D T true (deployedLeaf true) L v) ∧
      (∃ B, TimeoutGateAt H D T false (deployedLeaf false) B v) ∧
      ¬ FinalizedBy H D v ∧ FinalizedBy H D w


/-- **EXACTLY ONE OF THE FOUR (FLAG, LEAF) COMBINATIONS IS UNSOUND.**  The gate with flag `b`
and leaf `leaf` is sound over all append-only, time-ordered histories (an accepted proof means
the value never finalizes) iff `b = true` or `leaf = .endRoot`.

* `(true, beginRoot)` is the deployed begin branch, and `(false, endRoot)` the deployed end
  branch.
* `(true, endRoot)` is the harmless swap (`begin_branch_with_end_root_sound`): `begin ⊆ end`,
  so an end root proves more.
* `(false, beginRoot)` is the dangerous swap, and it is the only failure.

So `deployedLeaf` matters in exactly one direction. -/
abbrev Properties.timeoutGate_sound_iff_not_end_flag_begin_leaf (b : Bool) (leaf : ImtRootLeaf) :=
  (∀ (H : BatchHistory) (D T n : ℕ) (v : UInt256), AppendOnly H → TimeOrdered H →
      TimeoutGateAt H D T b leaf n v → ¬ FinalizedBy H D v) ↔
    (b = true ∨ leaf = .endRoot)


end AttackVectors.TimeoutSoundness
