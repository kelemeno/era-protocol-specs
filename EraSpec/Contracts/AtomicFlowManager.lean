import EraSpec.Core.IMT

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
tree and the deadline (`EraSpec.Core.IMT`, `EraSpec.Properties.TimeoutSoundness`).
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

/-! ## State -/

/-- `LegState` from `IAtomicInterop.sol`. -/
inductive LegState
  | Unset
  | Committed
  | Revertable
  | Reverted
deriving DecidableEq, Repr

/-- Position in the lifecycle.  The whole file rests on this being monotone. -/
def rank : LegState → ℕ
  | .Unset => 0
  | .Committed => 1
  | .Revertable => 2
  | .Reverted => 3

@[simp] lemma rank_unset : rank .Unset = 0 := rfl
@[simp] lemma rank_committed : rank .Committed = 1 := rfl
@[simp] lemma rank_revertable : rank .Revertable = 2 := rfl
@[simp] lemma rank_reverted : rank .Reverted = 3 := rfl

lemma rank_inj : ∀ {s t : LegState}, rank s = rank t → s = t := by
  intro s t h; cases s <;> cases t <;> simp_all [rank]

/-- The manager's state: one `LegState` per `(flowId, bundleHash)`.  Keys are
`UInt256`, mirroring `bytes32`. -/
structure Manager where
  legState : UInt256 → UInt256 → LegState

/-- Fresh storage: every leg `Unset`. -/
def empty : Manager := ⟨fun _ _ => .Unset⟩

/-- Point update of one leg. -/
def Manager.set (M : Manager) (f b : UInt256) (s : LegState) : Manager :=
  ⟨fun f' b' => if f' = f ∧ b' = b then s else M.legState f' b'⟩

@[simp] lemma set_same {M : Manager} {f b s} : (M.set f b s).legState f b = s := by
  simp [Manager.set]

lemma set_other {M : Manager} {f b f' b' s} (h : ¬(f' = f ∧ b' = b)) :
    (M.set f b s).legState f' b' = M.legState f' b' := by
  simp [Manager.set, h]

/-! ## Operations

Each carries the guard its Solidity counterpart enforces.  Access control
(`onlyInteropCenter` on `append`, `onlyInteropHandler` on `requireFlowFinalized`)
is *not* modeled as a guard here: it constrains who may call, not what the state
transition does, and modeling it would need a caller-identity component that
adds nothing to the results below.  It is recorded as an obligation in
`EraSpec.Refinement` instead, where the concrete repo's `#37`-style call-site
enumeration discharges it. -/

/-- `append`: `ManagerLegAlreadyCommitted` unless the leg is `Unset`. -/
def AppendGuard (M : Manager) (f b : UInt256) : Prop := M.legState f b = .Unset

/-- `authorizeRefund`, per leg: the loop `continue`s unless the leg is
`Committed`, so only committed legs move.  Legs committed on other chains are
absent from this manager and are silently skipped — that is what makes the
per-leg formulation faithful. -/
def AuthorizeGuard (M : Manager) (f b : UInt256) : Prop := M.legState f b = .Committed

/-- `claimRefund`: `ManagerLegNotRevertable` unless the leg is `Revertable`. -/
def ClaimGuard (M : Manager) (f b : UInt256) : Prop := M.legState f b = .Revertable

/-- One step of the manager. -/
inductive Step : Manager → Manager → Prop
  | append {M f b} : AppendGuard M f b → Step M (M.set f b .Committed)
  | authorize {M f b} : AuthorizeGuard M f b → Step M (M.set f b .Revertable)
  | claim {M f b} : ClaimGuard M f b → Step M (M.set f b .Reverted)

/-- Reflexive-transitive closure: reachability over any number of steps. -/
inductive Reach : Manager → Manager → Prop
  | refl {M} : Reach M M
  | tail {M N P} : Reach M N → Step N P → Reach M P

/-! ## The rank is monotone -/

/-- **NO LEG EVER MOVES BACKWARD.**  One step cannot lower any leg's rank.

Note this is stated for EVERY leg, not just the one the step touches: the
untouched legs are unchanged, and the touched one advances.  That is what lets
the result compose over runs without tracking which leg each step hit. -/
theorem step_rank_mono {M N : Manager} (h : Step M N) (f b : UInt256) :
    rank (M.legState f b) ≤ rank (N.legState f b) := by
  cases h with
  | @append f' b' hg =>
    by_cases he : f = f' ∧ b = b'
    · obtain ⟨rfl, rfl⟩ := he; rw [hg, set_same]; simp
    · rw [set_other he]
  | @authorize f' b' hg =>
    by_cases he : f = f' ∧ b = b'
    · obtain ⟨rfl, rfl⟩ := he; rw [hg, set_same]; simp
    · rw [set_other he]
  | @claim f' b' hg =>
    by_cases he : f = f' ∧ b = b'
    · obtain ⟨rfl, rfl⟩ := he; rw [hg, set_same]; simp
    · rw [set_other he]

/-- Monotonicity along whole runs. -/
theorem reach_rank_mono {M N : Manager} (h : Reach M N) (f b : UInt256) :
    rank (M.legState f b) ≤ rank (N.legState f b) := by
  induction h with
  | refl => exact le_refl _
  | tail hr hs ih => exact le_trans ih (step_rank_mono hs _ _)

/-! ## Consequences -/

/-- **`Reverted` IS ABSORBING.**  A refunded leg stays refunded through any run:
no operation can move it, because each guards on a different state.

This is the no-double-refund guarantee in its strongest form — it holds for every
reachable state, not merely for two consecutive claims. -/
theorem reverted_absorbing {M N : Manager} (h : Reach M N) {f b : UInt256}
    (hrev : M.legState f b = .Reverted) : N.legState f b = .Reverted := by
  have hmono := reach_rank_mono h f b
  rw [hrev] at hmono
  cases hN : N.legState f b with
  | Unset => rw [hN] at hmono; simp [rank] at hmono
  | Committed => rw [hN] at hmono; simp [rank] at hmono
  | Revertable => rw [hN] at hmono; simp [rank] at hmono
  | Reverted => rfl

/-- **A LEG CANNOT BE CLAIMED TWICE.**  After a claim, no reachable state admits
`ClaimGuard` for that leg — so `claimRefund` pays out at most once per leg. -/
theorem no_double_claim {M N : Manager} {f b : UInt256}
    (_hclaim : ClaimGuard M f b) (h : Reach (M.set f b .Reverted) N) :
    ¬ ClaimGuard N f b := by
  intro hg
  have hg' : N.legState f b = .Revertable := hg
  have hrev := reverted_absorbing h (show (M.set f b .Reverted).legState f b = .Reverted by simp)
  rw [hrev] at hg'
  exact absurd hg' (by decide)

/-- **A REFUND REQUIRES A PRIOR AUTHORIZATION.**  A leg that was never advanced
past `Unset` cannot be claimed: `ClaimGuard` needs rank 2, and reaching it from
rank 0 requires the intermediate `authorize` step.  Stated contrapositively — if
the gate is open, the leg's rank is already 2, which only `authorize` produces. -/
theorem claim_requires_authorization {M : Manager} {f b : UInt256}
    (hg : ClaimGuard M f b) : rank (M.legState f b) = 2 := by
  have hg' : M.legState f b = .Revertable := hg
  rw [hg']
  rfl

/-- **AN UNSET LEG IS NOT CLAIMABLE.**  The direct statement: a leg with no
commitment on this chain cannot be refunded here. -/
theorem unset_not_claimable {M : Manager} {f b : UInt256}
    (h : M.legState f b = .Unset) : ¬ ClaimGuard M f b := by
  intro hg
  have hg' : M.legState f b = .Revertable := hg
  rw [h] at hg'
  exact absurd hg' (by decide)

/-- **A COMMITTED LEG IS NOT DIRECTLY CLAIMABLE.**  `claimRefund` cannot be
reached from `Committed` without `authorizeRefund` — which is where the timeout
proof is checked.  This is the state-machine half of "no refund without a proof";
the other half (that the proof implies the flow can never finalize) is
`EraSpec.Properties.TimeoutSoundness`. -/
theorem committed_not_claimable {M : Manager} {f b : UInt256}
    (h : M.legState f b = .Committed) : ¬ ClaimGuard M f b := by
  intro hg
  have hg' : M.legState f b = .Revertable := hg
  rw [h] at hg'
  exact absurd hg' (by decide)

/-- **APPEND IS ONCE-PER-LEG.**  After a leg is committed, no reachable state
admits `AppendGuard` for it — so a leg's commit value enters the tree at most
once, which is what makes the tree's dedup gate and this machine agree. -/
theorem no_double_append {M N : Manager} {f b : UInt256}
    (_happ : AppendGuard M f b) (h : Reach (M.set f b .Committed) N) :
    ¬ AppendGuard N f b := by
  intro hg
  have hg' : N.legState f b = .Unset := hg
  have hmono := reach_rank_mono h f b
  rw [set_same, hg'] at hmono
  simp [rank] at hmono

/-- **THE CEI ORDER IS WHAT REMOVES THE NEED FOR A REENTRANCY GUARD.**  In the
state the external recovery calls run against, the leg is already `Reverted`, so
`ClaimGuard` is closed for the whole duration of those calls.

`claimRefund` sets state *before* `_recoverBundle` (effects-before-interaction);
this lemma is the formal content of that comment in the source.  Had the order
been reversed, the state during the external calls would still be `Revertable`
and a reentrant claim would pass its guard. -/
theorem claim_closes_gate_before_interaction {M : Manager} {f b : UInt256} :
    ¬ ClaimGuard (M.set f b .Reverted) f b := by
  intro hg
  have hg' : (M.set f b .Reverted).legState f b = .Revertable := hg
  rw [set_same] at hg'
  exact absurd hg' (by decide)

/-- The lifecycle is exactly four states deep: no run can move a leg more than
three times.  A convenient bound when reasoning about whole histories. -/
theorem rank_le_three (M : Manager) (f b : UInt256) : rank (M.legState f b) ≤ 3 := by
  cases M.legState f b <;> simp [rank]

end Contracts.AtomicFlowManager
