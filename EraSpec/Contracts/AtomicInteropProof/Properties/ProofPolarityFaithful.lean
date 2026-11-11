import EraSpec.Contracts.AtomicInteropProof.Specs.ProofPolarityFaithful

/-!
# Properties: proof polarity with the declared chain kept apart

Statements over `../Specs/ProofPolarityFaithful.lean`.  Proofs:
`../Proofs/ProofPolarityFaithful.lean`.

`AttackVectors.ProofPolarity` proves its theorems about one chain value `srcOf v` and
reads them as saying that the finality-side check A (`proofs[i].sourceChainId ==
legSourceChainIds[i]`) "adds nothing" under honest insertion.  With the declared chain
`decl v` modelled separately, as the pinned contract has it:

* **The deployed pair of checks is exclusive with no premise at all**
  (`CheckedGatesExclusive`): both gates pin to `decl v`, so finality needs `v` in
  `decl v`'s tree and refund needs it absent there.
* **Check A is NOT redundant at the pin, even under honest insertion.**  Removing it
  allows execution plus refund (a double mint) for a live leg exactly when the leg is
  misdeclared, `decl v ≠ srcOf v` (`UncheckedDoubleMintIffMisdeclared`), and the pinned
  `append` reaches such a state (`PinnedMisdeclaredDoubleMint`).  So the reading of
  `ProofPolarity.inclusion_self_binds` ("the explicit equality check adds nothing on
  this path") and the source comment at `AtomicFlowManager.sol:117-119` are false of
  the pinned contract.
* **The refund pin is to `decl v`, not `srcOf v`.**  A committed leg pinned to its
  declared chain can still have an absence witness (`RefundNotBlockedWhenPinnedToDeclared`);
  the refund is blocked exactly when `decl v = srcOf v`
  (`RefundBlockedIffDeclaredIsSource`).  This replaces the reading of
  `ProofPolarity.refund_blocked_when_chain_pinned`, whose premise `c = srcOf v` is not
  the contract's pin.
* **Check A is redundant exactly under `DeclaredInsertion`**
  (`UncheckedExclusiveUnderDeclared`), which the upgrade's `append` establishes on every
  honest chain (`UpgradeReachDeclared`, `UpgradeCheckARedundant`).  At the upgrade
  `decl v = srcOf v` holds for every committed value (`UpgradeExcludesMisdeclared`),
  so the original model's identification becomes accurate there.
-/

namespace AttackVectors.ProofPolarityFaithful

/-- **THE PINNED `append` PRESERVES HONEST INSERTION.**  Every state honest chains
reach under the pinned `append` satisfies `HonestInsertion`: the bundle hash bakes in
the committing chain. -/
def Properties.PinnedReachHonest : Prop :=
  ∀ (Chain Value : Type) (srcOf : Value → Chain) (tree : Chain → Set Value),
    PinnedReach srcOf tree → HonestInsertion srcOf tree

/-- **THE UPGRADED `append` ALSO ESTABLISHES DECLARED INSERTION.**  With
`legSourceChainIds[legIndex] == block.chainid` checked at commit time, every reachable
state satisfies both `HonestInsertion` and `DeclaredInsertion`. -/
def Properties.UpgradeReachDeclared : Prop :=
  ∀ (Chain Value : Type) (srcOf decl : Value → Chain) (tree : Chain → Set Value),
    UpgradeReach srcOf decl tree → HonestInsertion srcOf tree ∧ DeclaredInsertion decl tree

/-- **THE DEPLOYED CHECKS ARE EXCLUSIVE, WITH NO PREMISE.**  With check A and check B
both present, no flow is both finalized (every leg proved against its declared chain)
and refunded (some leg proved absent from its declared chain).  No honesty assumption
about any chain is used. -/
def Properties.CheckedGatesExclusive : Prop :=
  ∀ (Chain Value : Type) (decl : Value → Chain) (tree : Chain → Set Value) (legs : List Value)
    (pc : Value → Chain),
    FlowFinalizedChecked decl tree legs pc → ¬ FlowRefunded decl tree legs

/-- **WITHOUT CHECK A, A LIVE LEG IS DOUBLE-MINTED EXACTLY WHEN IT IS MISDECLARED.**
Under honest insertion: leg `v` passes the finality gate with check A removed at some
chain AND passes the refund gate at some chain, iff `v` is committed on its real source
chain and its flow declares a different chain. -/
def Properties.UncheckedDoubleMintIffMisdeclared : Prop :=
  ∀ (Chain Value : Type) (srcOf decl : Value → Chain) (tree : Chain → Set Value) (v : Value),
    HonestInsertion srcOf tree →
      (((∃ c, FinalityUnchecked tree v c) ∧ ∃ c, RefundChecked decl tree v c)
        ↔ (v ∈ tree (srcOf v) ∧ decl v ≠ srcOf v))

/-- **COUNTERMODEL: AT THE PIN, CHECK A IS LOAD-BEARING UNDER HONEST INSERTION.**  Chain
`true` commits a leg under a flow that declares chain `false`; the pinned `append`
accepts it.  The state satisfies `HonestInsertion` but not `DeclaredInsertion`.  With
check A removed the one-leg flow is finalized (proof against chain `true`) AND refunded
(absence at chain `false`); with check A present, finality fails for every choice of
proof chains.  So the "defense-in-depth" reading of the finality-side check is false
of the pinned contract. -/
def Properties.PinnedMisdeclaredDoubleMint : Prop :=
  PinnedReach cmSrc cmTree ∧ HonestInsertion cmSrc cmTree ∧ ¬ DeclaredInsertion cmDecl cmTree
    ∧ () ∈ cmTree (cmSrc ()) ∧ cmDecl () ≠ cmSrc ()
    ∧ FlowFinalizedUnchecked cmTree [()] cmSrc ∧ FlowRefunded cmDecl cmTree [()]
    ∧ ∀ pc : Unit → Bool, ¬ FlowFinalizedChecked cmDecl cmTree [()] pc

/-- **COUNTERMODEL: PINNING THE REFUND PROOF TO THE DECLARED CHAIN DOES NOT BLOCK IT.**
In the same reachable pinned state, the leg is committed on its real source chain, the
absence proof is pinned to the leg's declared chain (check B passes), and the leg is
absent there.  This is the case `ProofPolarity.refund_blocked_when_chain_pinned`
excludes by writing the pin as `c = srcOf v`. -/
def Properties.RefundNotBlockedWhenPinnedToDeclared : Prop :=
  PinnedReach cmSrc cmTree ∧ () ∈ cmTree (cmSrc ()) ∧ RefundChecked cmDecl cmTree () (cmDecl ())

/-- **WHEN THE REFUND OF A LIVE LEG IS BLOCKED.**  Under honest insertion, a leg
committed on its real source chain has no accepted refund proof iff its declared chain
is its real source chain.  (When it is not, finality is blocked instead, by check A.) -/
def Properties.RefundBlockedIffDeclaredIsSource : Prop :=
  ∀ (Chain Value : Type) (srcOf decl : Value → Chain) (tree : Chain → Set Value) (v : Value),
    HonestInsertion srcOf tree → v ∈ tree (srcOf v) →
      ((¬ ∃ c, RefundChecked decl tree v c) ↔ decl v = srcOf v)

/-- **CHECK A IS REDUNDANT EXACTLY WHERE `DeclaredInsertion` HOLDS.**  If every tree
holds only legs declared on its own chain, a flow finalized without check A is
finalized with it, and so is not refunded. -/
def Properties.UncheckedExclusiveUnderDeclared : Prop :=
  ∀ (Chain Value : Type) (decl : Value → Chain) (tree : Chain → Set Value) (legs : List Value)
    (pc : Value → Chain),
    DeclaredInsertion decl tree → FlowFinalizedUnchecked tree legs pc →
      FlowFinalizedChecked decl tree legs pc ∧ ¬ FlowRefunded decl tree legs

/-- **AT THE UPGRADE THE "DEFENSE-IN-DEPTH" READING HOLDS.**  In every state honest
chains reach under the upgraded `append`, check A adds nothing: a flow finalized
without it is finalized with it, and is not refunded. -/
def Properties.UpgradeCheckARedundant : Prop :=
  ∀ (Chain Value : Type) (srcOf decl : Value → Chain) (tree : Chain → Set Value)
    (legs : List Value) (pc : Value → Chain),
    UpgradeReach srcOf decl tree → FlowFinalizedUnchecked tree legs pc →
      FlowFinalizedChecked decl tree legs pc ∧ ¬ FlowRefunded decl tree legs

/-- **AT THE UPGRADE, DECLARED = REAL ON COMMITTED VALUES.**  Every committed value's
declared chain is its real source chain, which is the identification
`ProofPolarity` makes everywhere. -/
def Properties.UpgradeExcludesMisdeclared : Prop :=
  ∀ (Chain Value : Type) (srcOf decl : Value → Chain) (tree : Chain → Set Value)
    (c : Chain) (v : Value),
    UpgradeReach srcOf decl tree → v ∈ tree c → decl v = srcOf v

/-- **THE UPGRADE PREMISES ARE SATISFIABLE, NON-VACUOUSLY.**  The leg declared on its
real source chain is committed by the upgraded `append`, and the one-leg flow is
finalized with check A (so the premise of `UpgradeCheckARedundant` holds). -/
def Properties.UpgradeFinalitySatisfiable : Prop :=
  UpgradeReach cmSrc cmSrc cmTree ∧ FlowFinalizedUnchecked cmTree [()] cmSrc
    ∧ FlowFinalizedChecked cmSrc cmTree [()] cmSrc

end AttackVectors.ProofPolarityFaithful
