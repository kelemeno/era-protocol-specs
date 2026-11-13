import EraSpec.Contracts.AtomicFlowManager.Specs.Model

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false


/-!
# Contract spec: `AtomicFlowManager`

The per-leg state machine of the flow manager, and the refund guarantees that
follow from its shape alone.

## What this file is about

`AtomicFlowManager` holds one piece of mutable state per leg:

    mapping(bytes32 flowId => mapping(bytes32 bundleHash => LegState)) _state

and three operations move it: `append` (send time), `authorizeRefund` (timeout
proven), `claimRefund` (funds returned).  Every refund guarantee the contract
offers is a property of *this* machine — no Merkle proof, no tree, no timestamp
is involved once the proof has been accepted.

That separation is worth making explicit, because the two halves fail
differently.  Whether a refund is *justified* is a question about the commitment
tree and the deadline (`EraSpec.Contracts.IndexedMerkleTree.Specs.Model`, `EraSpec.Contracts.AtomicInteropProof.Properties.TimeoutSoundness`).
Whether a justified refund can be taken *twice* is a question about this state
machine, and the answer here does not depend on the proof system at all.

## The rank argument

Rather than enumerate reachable histories, every result below comes from one
observation: the three operations only ever move a leg *up* the chain

    Unset → Committed → Revertable → Reverted

because each guards on the exact predecessor state.  So `rank` is monotone along
any run, `Reverted` is a fixed point, and no-double-refund is a corollary rather
than a separate argument.  This is the state-machine analogue of the
checked-then-set nullifier pattern, and it is why `claimRefund` needs no
reentrancy guard: the flip to `Reverted` precedes the external calls, so a
reentrant claim meets a leg that is no longer `Revertable`.  That last argument
is about the order of operations inside `claimRefund`, which `Step.claim` cannot
express because it is a single atomic transition.  It is proved over a model with
reentrant callbacks in `EraSpec.Contracts.AtomicFlowManager.Properties.ModelStrong`
(`claim_order_decides_double_payout`).
-/

namespace Contracts.AtomicFlowManager


abbrev Properties.rank_unset :=
  rank .Unset = 0

abbrev Properties.rank_committed :=
  rank .Committed = 1

abbrev Properties.rank_revertable :=
  rank .Revertable = 2

abbrev Properties.rank_reverted :=
  rank .Reverted = 3


abbrev Properties.rank_inj :=
  ∀ {s t : LegState}, rank s = rank t → s = t


abbrev Properties.set_same {M : Manager} {f b s} :=
  (M.set f b s).legState f b = s


abbrev Properties.set_other {M : Manager} {f b f' b' s} (h : ¬(f' = f ∧ b' = b)) :=
  (M.set f b s).legState f' b' = M.legState f' b'


/-! ## The rank is monotone -/

/-- **NO LEG EVER MOVES BACKWARD.**  One step cannot lower any leg's rank.

Note this is stated for EVERY leg, not just the one the step touches: the
untouched legs are unchanged, and the touched one advances.  That is what lets
the result compose over runs without tracking which leg each step hit. -/
abbrev Properties.step_rank_mono {M N : Manager} (h : Step M N) (f b : UInt256) :=
  rank (M.legState f b) ≤ rank (N.legState f b)


/-- Monotonicity along whole runs. -/
abbrev Properties.reach_rank_mono {M N : Manager} (h : Reach M N) (f b : UInt256) :=
  rank (M.legState f b) ≤ rank (N.legState f b)


/-! ## Consequences -/

/-- **`Reverted` IS ABSORBING.**  A refunded leg stays refunded through any run:
no operation can move it, because each guards on a different state.

This is the no-double-refund guarantee in its strongest form — it holds for every
reachable state, not merely for two consecutive claims. -/
abbrev Properties.reverted_absorbing {M N : Manager} (h : Reach M N) {f b : UInt256}
    (hrev : M.legState f b = .Reverted) :=
  N.legState f b = .Reverted


/-- **A LEG CANNOT BE CLAIMED TWICE.**  After a claim, no reachable state admits
`ClaimGuard` for that leg — so `claimRefund` pays out at most once per leg. -/
abbrev Properties.no_double_claim {M N : Manager} {f b : UInt256}
    (_hclaim : ClaimGuard M f b) (h : Reach (M.set f b .Reverted) N) :=
  ¬ ClaimGuard N f b


/-- **AN OPEN CLAIM GATE MEANS RANK 2.**  A fact about one state: if `ClaimGuard`
holds, the leg is `Revertable`, whose rank is 2.  The statement mentions no run and
no `authorize` step.  It holds just as well for a manager set to `Revertable`
directly.  The history claims are proved in
`EraSpec.Contracts.AtomicFlowManager.Properties.ModelStrong`.  Only `authorize`
produces `Revertable` (`step_into_revertable_is_authorize`).  On every run, every
claim of a leg that starts below `Revertable` comes after an `authorize` of that
leg (`claim_event_preceded_by_authorize`; `Reach` form
`claimable_reach_passed_authorize`). -/
abbrev Properties.claim_requires_authorization {M : Manager} {f b : UInt256}
    (hg : ClaimGuard M f b) :=
  rank (M.legState f b) = 2


/-- **AN UNSET LEG IS NOT CLAIMABLE IN THE SAME STATE.**  A fact about one state:
`Unset ≠ Revertable`.  It does not say the leg can never be refunded here: a run
makes an `Unset` leg claimable in two steps.  Every such run takes exactly those two
steps on the leg, `append` and then `authorize`
(`ModelStrong.Properties.unset_claimable_trace`). -/
abbrev Properties.unset_not_claimable {M : Manager} {f b : UInt256}
    (h : M.legState f b = .Unset) :=
  ¬ ClaimGuard M f b


/-- **A COMMITTED LEG IS NOT CLAIMABLE IN THE SAME STATE.**  A fact about one
state: `Committed ≠ Revertable`.  The run-level reading is that `claimRefund` cannot
be reached from `Committed` without `authorizeRefund`, which is where the timeout
proof is checked.  That reading is `ModelStrong.Properties.committed_claimable_trace`:
on every run from a `Committed` leg to a claimable one, exactly one step touches the
leg, and that step is `authorize`.  This is the state-machine half of "no refund
without a proof".  The other half, that the proof implies the flow can never
finalize, is `EraSpec.Contracts.AtomicInteropProof.Properties.TimeoutSoundness`. -/
abbrev Properties.committed_not_claimable {M : Manager} {f b : UInt256}
    (h : M.legState f b = .Committed) :=
  ¬ ClaimGuard M f b


/-- **APPEND IS ONCE-PER-LEG.**  After a leg is committed, no reachable state
admits `AppendGuard` for it — so a leg's commit value enters the tree at most
once, which is what makes the tree's dedup gate and this machine agree. -/
abbrev Properties.no_double_append {M N : Manager} {f b : UInt256}
    (_happ : AppendGuard M f b) (h : Reach (M.set f b .Committed) N) :=
  ¬ AppendGuard N f b


/-- **AFTER THE WRITE, THE CLAIM GATE IS CLOSED.**  A fact about one state: in
`M.set f b .Reverted` the leg is not claimable (`set_same` and
`Reverted ≠ Revertable`).

This lemma is not the formal content of the effects-before-interaction comment in
`claimRefund`.  `Step.claim` is one atomic transition with no external-call phase.
So this model cannot say which state the recovery calls run against, and the lemma
would hold whatever order the source used.  The ordering claim is proved in
`EraSpec.Contracts.AtomicFlowManager.Properties.ModelStrong`, over a model whose
claims make reentrant callbacks.  Under the deployed order a claim's callback cannot
claim the same leg (`writeFirst_callback_never_reclaims`), and each leg pays out at
most once (`writeFirst_payouts_exact`).  Had the order been reversed, a reentrant
claim would pass its guard, and one leg could be paid out any number of times
(`writeAfter_unbounded_payouts`, `claim_order_decides_double_payout`). -/
abbrev Properties.claim_closes_gate_before_interaction {M : Manager} {f b : UInt256} :=
  ¬ ClaimGuard (M.set f b .Reverted) f b


/-- **RANKS ARE AT MOST THREE.**  A fact about `rank`'s four values.  It holds for
every state, reachable or not, and mentions no run.  On its own it does not bound
how often a run moves a leg, because `step_rank_mono` is only `≤`.  The run-level
bound is `ModelStrong.Properties.legRun_changes_le_three`: no run changes a leg's
state more than `3 - rank` times, counting from the leg's starting state.  The count
is exactly the rank gain (`legRun_changes_eq_rank_gain`). -/
abbrev Properties.rank_le_three (M : Manager) (f b : UInt256) :=
  rank (M.legState f b) ≤ 3


end Contracts.AtomicFlowManager
