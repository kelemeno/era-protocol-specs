import EraSpec.Contracts.AtomicFlowManager.Properties.Model
import EraSpec.Contracts.IndexedMerkleTree.Proofs.Model


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
reentrant claim meets a leg that is no longer `Revertable`.
-/

namespace Contracts.AtomicFlowManager


@[simp] lemma rank_unset :
    Properties.rank_unset :=
  rfl

@[simp] lemma rank_committed :
    Properties.rank_committed :=
  rfl

@[simp] lemma rank_revertable :
    Properties.rank_revertable :=
  rfl

@[simp] lemma rank_reverted :
    Properties.rank_reverted :=
  rfl


lemma rank_inj :
    Properties.rank_inj := by
  intro s t h; cases s <;> cases t <;> simp_all [rank]


@[simp] lemma set_same {M : Manager} {f b s} :
    Properties.set_same (M := M) (f := f) (b := b) (s := s) := by
  unfold Properties.set_same
  simp [Manager.set]


lemma set_other {M : Manager} {f b f' b' s} (h : ¬(f' = f ∧ b' = b)) :
    Properties.set_other (M := M) (f := f) (b := b) (f' := f') (b' := b') (s := s) (h := h) := by
  unfold Properties.set_other
  simp [Manager.set, h]


/-! ## The rank is monotone -/

/-- **NO LEG EVER MOVES BACKWARD.**  One step cannot lower any leg's rank.

Note this is stated for EVERY leg, not just the one the step touches: the
untouched legs are unchanged, and the touched one advances.  That is what lets
the result compose over runs without tracking which leg each step hit. -/
theorem step_rank_mono {M N : Manager} (h : Step M N) (f b : UInt256) :
    Properties.step_rank_mono (M := M) (N := N) (h := h) (f := f) (b := b) := by
  unfold Properties.step_rank_mono
  cases h <;> rename_i hg <;> simp only [Manager.set] <;> split_ifs with he
  all_goals first | exact le_rfl | (obtain ⟨rfl, rfl⟩ := he; rw [hg]; decide)


/-- Monotonicity along whole runs. -/
theorem reach_rank_mono {M N : Manager} (h : Reach M N) (f b : UInt256) :
    Properties.reach_rank_mono (M := M) (N := N) (h := h) (f := f) (b := b) := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact ih.trans (step_rank_mono hs _ _)


/-! ## Consequences -/

/-- **`Reverted` IS ABSORBING.**  A refunded leg stays refunded through any run:
no operation can move it, because each guards on a different state.

This is the no-double-refund guarantee in its strongest form — it holds for every
reachable state, not merely for two consecutive claims. -/
theorem reverted_absorbing {M N : Manager} (h : Reach M N) {f b : UInt256}
    (hrev : M.legState f b = .Reverted) :
    Properties.reverted_absorbing (M := M) (N := N) (h := h) (f := f) (b := b) (hrev := hrev) := by
  have hmono : rank .Reverted ≤ rank (N.legState f b) := hrev ▸ reach_rank_mono h f b
  unfold Properties.reverted_absorbing
  revert hmono
  cases N.legState f b <;> decide


/-- **A LEG CANNOT BE CLAIMED TWICE.**  After a claim, no reachable state admits
`ClaimGuard` for that leg — so `claimRefund` pays out at most once per leg. -/
theorem no_double_claim {M N : Manager} {f b : UInt256}
    (_hclaim : ClaimGuard M f b) (h : Reach (M.set f b .Reverted) N) :
    Properties.no_double_claim (M := M) (N := N) (f := f) (b := b) (_hclaim := _hclaim) (h := h) := by
  intro hg
  simp [ClaimGuard, reverted_absorbing h set_same] at hg


/-- **A REFUND REQUIRES A PRIOR AUTHORIZATION.**  A leg that was never advanced
past `Unset` cannot be claimed: `ClaimGuard` needs rank 2, and reaching it from
rank 0 requires the intermediate `authorize` step.  Stated contrapositively — if
the gate is open, the leg's rank is already 2, which only `authorize` produces. -/
theorem claim_requires_authorization {M : Manager} {f b : UInt256}
    (hg : ClaimGuard M f b) :
    Properties.claim_requires_authorization (M := M) (f := f) (b := b) (hg := hg) :=
  congrArg rank hg


/-- **AN UNSET LEG IS NOT CLAIMABLE.**  The direct statement: a leg with no
commitment on this chain cannot be refunded here. -/
theorem unset_not_claimable {M : Manager} {f b : UInt256}
    (h : M.legState f b = .Unset) :
    Properties.unset_not_claimable (M := M) (f := f) (b := b) (h := h) := by
  intro hg
  simp [ClaimGuard, h] at hg


/-- **A COMMITTED LEG IS NOT DIRECTLY CLAIMABLE.**  `claimRefund` cannot be
reached from `Committed` without `authorizeRefund` — which is where the timeout
proof is checked.  This is the state-machine half of "no refund without a proof";
the other half (that the proof implies the flow can never finalize) is
`EraSpec.Contracts.AtomicInteropProof.Properties.TimeoutSoundness`. -/
theorem committed_not_claimable {M : Manager} {f b : UInt256}
    (h : M.legState f b = .Committed) :
    Properties.committed_not_claimable (M := M) (f := f) (b := b) (h := h) := by
  intro hg
  simp [ClaimGuard, h] at hg


/-- **APPEND IS ONCE-PER-LEG.**  After a leg is committed, no reachable state
admits `AppendGuard` for it — so a leg's commit value enters the tree at most
once, which is what makes the tree's dedup gate and this machine agree. -/
theorem no_double_append {M N : Manager} {f b : UInt256}
    (_happ : AppendGuard M f b) (h : Reach (M.set f b .Committed) N) :
    Properties.no_double_append (M := M) (N := N) (f := f) (b := b) (_happ := _happ) (h := h) := by
  intro hg
  have hset : (M.set f b .Committed).legState f b = .Committed := set_same
  have hmono : rank .Committed ≤ rank (N.legState f b) := hset ▸ reach_rank_mono h f b
  simp [show N.legState f b = .Unset from hg, rank] at hmono


/-- **THE CEI ORDER IS WHAT REMOVES THE NEED FOR A REENTRANCY GUARD.**  In the
state the external recovery calls run against, the leg is already `Reverted`, so
`ClaimGuard` is closed for the whole duration of those calls.

`claimRefund` sets state *before* `_recoverBundle` (effects-before-interaction);
this lemma is the formal content of that comment in the source.  Had the order
been reversed, the state during the external calls would still be `Revertable`
and a reentrant claim would pass its guard. -/
theorem claim_closes_gate_before_interaction {M : Manager} {f b : UInt256} :
    Properties.claim_closes_gate_before_interaction (M := M) (f := f) (b := b) := by
  intro hg
  simp [ClaimGuard] at hg


/-- The lifecycle is exactly four states deep: no run can move a leg more than
three times.  A convenient bound when reasoning about whole histories. -/
theorem rank_le_three (M : Manager) (f b : UInt256) :
    Properties.rank_le_three (M := M) (f := f) (b := b) := by
  unfold Properties.rank_le_three
  cases M.legState f b <;> decide


end Contracts.AtomicFlowManager
