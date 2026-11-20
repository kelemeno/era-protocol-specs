import EraSpec.Contracts.InteropHandlerBase.History.Specs.BundleStatusMachine

set_option linter.unusedVariables false

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
abbrev Properties.atomic_ledger_trivial (l : Ledger) (h : ∀ p ∈ l, p.1 = 0) :=
  releasedSum l = 0 ∧ collectedSum l = 0


/-- **AN ATOMIC BUNDLE HAS ONE ROUTE.**  From fresh, the only reachable states are fresh and
delivered.  This holds by the definition of `AtomicStep`, whose one edge is `Unreceived →
FullyExecuted`: that `verify` cannot fire for an atomic bundle is assumed there, not proved here.
It is derived from the deployed guards in `BundleStatusMachineStrong.NoProofKeepsBundleInAtomicMachine`
under a named no-proof premise, and that premise from the source chain in
`AtomicLegStaysAtomicAtDestinationOrClash`. -/
abbrev Properties.atomic_reach_two_states {t : Status} (h : AtomicReach .Unreceived t) :=
  t = .Unreceived ∨ t = .FullyExecuted


/-- **SO IT IS NEVER UNBUNDLED**, and `routes_exclusive` holds vacuously for it — the per-call route
does not exist on this path.  By the definition of `AtomicStep`, as for `atomic_reach_two_states`;
the derived form is `BundleStatusMachineStrong.NoProofKeepsBundleInAtomicMachine`. -/
abbrev Properties.atomic_never_unbundled :=
  ¬ AtomicReach .Unreceived .Unbundled


/-- And delivery-once for an atomic bundle needs only the BUNDLE machine: `FullyExecuted` is terminal
here too, since `AtomicStep` has no edge out of it (by definition: `AtomicStep` has one edge). -/
abbrev Properties.atomic_delivery_terminal {t : Status} :=
  ¬ AtomicStep .FullyExecuted t


end AttackVectors.BundleStatusMachine.History
