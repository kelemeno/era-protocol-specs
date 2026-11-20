import EraSpec.Contracts.InteropHandlerBase.Specs.BundleStatusMachineFaithful

/-!
# Properties: no delivery without a passing gate verdict

Statements about `EraSpec.Contracts.InteropHandlerBase.Specs.BundleStatusMachineFaithful`. Proofs
are in `EraSpec.Contracts.InteropHandlerBase.Proofs.BundleStatusMachineFaithful`.

* `DeliveryNeedsInclusionOrFlowGate`: along any sequence of transactions, with every target
  behaviour at every depth, a bundle hash none of whose entry-point calls presents a passing
  inclusion verdict or passes the flow gate stays `Unreceived` and has no committed effect. It is
  stated over the engine; `Reentrancy`'s `DeliveryNeedsTheGateAtV35` is its `b17415d20` form.

The pin `c67894b9` statements of this topic (the labelled machine, the never-published premise and
its countermodels) are in `History/Properties/BundleStatusMachineFaithful.lean`.
-/


namespace Contracts.InteropHandler.Faithful

open AttackVectors.BundleStatusMachine (Status)

/-! ## (b) Operationally -/

/-- **NO ACCEPTED INCLUSION PROOF AND NO PASSING FLOW GATE, NO DELIVERY.** From every state in which
bundle hash `h` is `Unreceived`, along every sequence of transactions none of whose entry-point
calls (at any depth, in any target) presents an inclusion proof accepted for `h` or passes the flow
gate for `h`: `h` ends `Unreceived`, and no committed effect belongs to `h`. None of its calls is
delivered and it never completes. -/
def Properties.DeliveryNeedsInclusionOrFlowGate : Prop :=
  ∀ (s : State) (h : BundleHash) (txs : List Tx), s.bundle h = .Unreceived →
    (∀ t ∈ txs, TxAll (fun e => ¬ ProvesInclusion h e ∧ ¬ PassesFlowGate h e) t) →
      (submitAll .deployed s txs).1.bundle h = .Unreceived ∧
        ∀ e ∈ (submitAll .deployed s txs).2, e.bundleHash ≠ h

end Contracts.InteropHandler.Faithful
