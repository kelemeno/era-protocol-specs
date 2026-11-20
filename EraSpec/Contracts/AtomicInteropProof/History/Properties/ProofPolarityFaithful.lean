import EraSpec.Core.Headline
import EraSpec.Contracts.AtomicInteropProof.History.Specs.ProofPolarityFaithful

/-!
# Properties (History): the pinned `append` and the misdeclared double mint (H1)

Statements over `../Specs/ProofPolarityFaithful.lean` and the current
`../../Specs/ProofPolarityFaithful.lean`, proved in `../Proofs/ProofPolarityFaithful.lean`.

**History.** The record of the H1 finding at `c67894b9`, not a claim about `b17415d20`, whose
`append` binds the declared chain (`AtomicFlowManager.sol:140-146`; the current results are
`AttackVectors.ProofPolarityFaithful.Properties.UpgradeReachDeclared`,
`UpgradeExcludesMisdeclared` and `UpgradeCheckARedundant`). Under the pinned `append`:

* every reachable state satisfies `HonestInsertion` (`PinnedReachHonest`);
* a leg committed on chain `true` under a flow declaring chain `false` is reachable, and with the
  finality-side check A removed the one-leg flow is both finalized and refunded
  (`PinnedMisdeclaredDoubleMint`), so check A was load-bearing at the pin;
* pinning the refund proof to the declared chain does not block it (`RefundNotBlockedWhenPinnedToDeclared`).
-/

namespace AttackVectors.ProofPolarityFaithful.History

/-- **THE PINNED `append` PRESERVES HONEST INSERTION.**  Every state honest chains
reach under the pinned `append` satisfies `HonestInsertion`: the bundle hash bakes in
the committing chain. -/
def Properties.PinnedReachHonest : Prop :=
  ∀ (Chain Value : Type) (srcOf : Value → Chain) (tree : Chain → Set Value),
    PinnedReach srcOf tree → HonestInsertion srcOf tree

/-- **COUNTERMODEL: AT THE PIN, CHECK A IS LOAD-BEARING UNDER HONEST INSERTION.**  Chain
`true` commits a leg under a flow that declares chain `false`; the pinned `append`
accepts it.  The state satisfies `HonestInsertion` but not `DeclaredInsertion`.  With
check A removed the one-leg flow is finalized (proof against chain `true`) AND refunded
(absence at chain `false`); with check A present, finality fails for every choice of
proof chains.  So the "defense-in-depth" reading of the finality-side check is false
of the pinned contract. -/
@[countermodel] def Properties.PinnedMisdeclaredDoubleMint : Prop :=
  PinnedReach cmSrc cmTree ∧ HonestInsertion cmSrc cmTree ∧ ¬ DeclaredInsertion cmDecl cmTree
    ∧ () ∈ cmTree (cmSrc ()) ∧ cmDecl () ≠ cmSrc ()
    ∧ FlowFinalizedUnchecked cmTree [()] cmSrc ∧ FlowRefunded cmDecl cmTree [()]
    ∧ ∀ pc : Unit → Bool, ¬ FlowFinalizedChecked cmDecl cmTree [()] pc

/-- **COUNTERMODEL: PINNING THE REFUND PROOF TO THE DECLARED CHAIN DOES NOT BLOCK IT.**
In the same reachable pinned state, the leg is committed on its real source chain, the
absence proof is pinned to the leg's declared chain (check B passes), and the leg is
absent there.  This is the case `ProofPolarity.refund_blocked_when_chain_pinned`
excludes by writing the pin as `c = srcOf v`. -/
@[countermodel] def Properties.RefundNotBlockedWhenPinnedToDeclared : Prop :=
  PinnedReach cmSrc cmTree ∧ () ∈ cmTree (cmSrc ()) ∧ RefundChecked cmDecl cmTree () (cmDecl ())

end AttackVectors.ProofPolarityFaithful.History
