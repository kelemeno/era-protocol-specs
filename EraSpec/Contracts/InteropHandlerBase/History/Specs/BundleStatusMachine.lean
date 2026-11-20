import EraSpec.Contracts.InteropHandlerBase.Specs.BundleStatusMachine

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

/-! ## The atomic sub-machine — a stronger guarantee, not a weaker one

Applying the same scope question to `routes_exclusive`: is it non-trivial for ATOMIC bundles?  It is
not, and the reason turns out to strengthen the atomic case rather than weaken it.

An atomic bundle cannot reach `Verified`: that edge is `verifyBundle`, which requires an L1 message
inclusion proof, and atomic bundles are never published to L1.  `unbundleBundle` requires
`Verified || Unbundled`.  So `Unbundled` is unreachable for an atomic bundle — it has exactly ONE
route, and `routes_exclusive` is satisfied vacuously for it.

That means the two machines divide by path:

* ATOMIC bundles — one route, so delivery-once follows from bundle-status terminality ALONE
  (`reach_from_fullyExecuted`).  The per-call machine is not needed: `executeAtomicBundle` writes every
  call `Executed` in one transaction, and there is no second transaction to worry about.
* PUBLIC bundles — two routes, so delivery-once genuinely needs BOTH machines, as recorded above.

So the earlier composition is not wrong for atomic bundles, it is more than they require.  Worth
knowing which half is load-bearing where.

The argument above is prose: `AtomicStep` below builds it into a definition.  Topic
`BundleStatusMachineStrong` proves it over the handler model, up to named clashes. -/

/-- **TAKEN AS A DEFINITION.**  The transitions available to an ATOMIC bundle, on the premise that
`verify` is unreachable for it (no L1 proof exists), and with it every edge that needs `Verified`.
That premise is assumed here, not proved: any one-edge relation gives the results stated about this
one.  Topic `BundleStatusMachineStrong` derives the sub-machine from the handler's guards
(`NoProofKeepsBundleInAtomicMachine`) and the premise from the source chain
(`AtomicLegStaysAtomicAtDestinationOrClash`). -/
inductive AtomicStep : Status → Status → Prop
  | executeAtomic : AtomicStep .Unreceived .FullyExecuted


inductive AtomicReach : Status → Status → Prop
  | refl (s : Status) : AtomicReach s s
  | tail {a b c : Status} : AtomicReach a b → AtomicStep b c → AtomicReach a c


end AttackVectors.BundleStatusMachine.History
