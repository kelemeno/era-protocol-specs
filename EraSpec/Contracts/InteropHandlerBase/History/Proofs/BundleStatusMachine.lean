import EraSpec.Contracts.InteropHandlerBase.History.Properties.BundleStatusMachine
import Mathlib.Tactic

/-! **History: a record of the interop pin `c67894b9`, not a claim about era-contracts `b17415d20`.**
The pin's argument for an atomic sub-machine was that an atomic bundle never reaches `Verified`,
because the only `Unreceived → Verified` edge was `verifyBundle`, which needs an L1 inclusion proof.
At `b17415d20` the L2 handler has `verifyAtomicBundle`
(`interop/interop-handler/L2InteropHandler.sol:83-92`), which runs the flow gate and marks an
atomic bundle `Verified`, and `executeAtomicBundle` admits a `Verified` bundle (`:61-78`,
`interop/interop-handler/InteropHandlerBase.sol:282-287`). So an atomic bundle can take
`Unreceived → Verified → Unbundled`, and `AtomicStep` does not describe `b17415d20`. The pin's
no-value rule for atomic calls (`_validateAtomicBundle`) is not in `b17415d20`'s `InteropCenter`
either; there a direct call's base-token value is refunded on the timeout path
(`atomic-interop/IAtomicFlowManager.sol:59`). Namespaces carry a `History` segment. -/

namespace AttackVectors.BundleStatusMachine.History

open AttackVectors.BundleStatusMachine

/-! ### Scope: where the no-inflation result is non-trivial

`_validateAtomicBundle` rejects any call carrying native value:

    if (_bundle.calls[i].value != 0) revert AtomicBundleCallCarriesValue(i, _bundle.calls[i].value);

and `calls[i].value` is exactly the `interopCallValue` summed into `totalBurnedCallsValue`
(`InteropCenter.sol:738`).  So for an ATOMIC bundle every entry of the ledger is zero and both sums
vanish — the inequality holds trivially and says nothing.

The result above is therefore about the PUBLIC interop path.  That is not a defect in either: atomic
legs deliberately move value through the asset router as `indirectCallMessageValue`, precisely because
`IAtomicRecoverable.recoverAtomicCall` can reverse an asset-router deposit but cannot reverse a
base-token transfer.  Banning native value is what keeps the timeout path meaningful for them, and
`RecoveryLimits` is where that path's own limits live.

Stating this because the inequality reads like a global conservation law and is not one. -/

/-- An atomic bundle's ledger is all zeros, so both sides vanish. -/
theorem atomic_ledger_trivial (l : Ledger) (h : ∀ p ∈ l, p.1 = 0) :
    Properties.atomic_ledger_trivial (l := l) (h := h) := by
  unfold Properties.atomic_ledger_trivial
  exact
    by
      induction l with
      | nil => exact ⟨rfl, rfl⟩
      | cons hd tl ih =>
        obtain ⟨v, st⟩ := hd
        have hv : v = 0 := h (v, st) (List.mem_cons_self ..)
        have htl := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
        subst hv
        constructor
        · by_cases hst : st = CallStatus.Executed <;> simp [releasedSum, hst, htl.1]
        · simp [collectedSum, htl.2]


/-- **AN ATOMIC BUNDLE HAS ONE ROUTE.**  From fresh, the only reachable states are fresh and
delivered. -/
theorem atomic_reach_two_states {t : Status} (h : AtomicReach .Unreceived t) :
    Properties.atomic_reach_two_states (t := t) (h := h) := by
  unfold Properties.atomic_reach_two_states
  exact
    by
      induction h with
      | refl => exact Or.inl rfl
      | tail _ hstep _ => cases hstep; exact Or.inr rfl


/-- **SO IT IS NEVER UNBUNDLED**, and `routes_exclusive` holds vacuously for it — the per-call route
does not exist on this path. -/
theorem atomic_never_unbundled :
    Properties.atomic_never_unbundled := by
  unfold Properties.atomic_never_unbundled
  exact
    by
      intro h
      rcases atomic_reach_two_states h with h1 | h1 <;> exact absurd h1 (by decide)


/-- And delivery-once for an atomic bundle needs only the BUNDLE machine: `FullyExecuted` is terminal
here too, since `AtomicStep` has no edge out of it. -/
theorem atomic_delivery_terminal {t : Status} :
    Properties.atomic_delivery_terminal (t := t) := by
  unfold Properties.atomic_delivery_terminal
  exact
    by
      rintro ⟨⟩


end AttackVectors.BundleStatusMachine.History
