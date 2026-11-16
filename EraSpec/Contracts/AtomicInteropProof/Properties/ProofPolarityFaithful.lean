import EraSpec.Contracts.AtomicInteropProof.Specs.ProofPolarityFaithful

/-!
# Properties: proof polarity with the declared chain kept apart

Statements over `../Specs/ProofPolarityFaithful.lean`.  Proofs:
`../Proofs/ProofPolarityFaithful.lean`.

`AttackVectors.ProofPolarity` proves its theorems about one chain value `srcOf v` and
reads them as saying that the finality-side check A (`proofs[i].sourceChainId ==
legSourceChainIds[i]`) "adds nothing" under honest insertion.  With the declared chain
`decl v` modelled separately, as the pinned contract has it:

* **The pair of checks is exclusive with no honesty premise, in this abstraction**
  (`CheckedGatesExclusive`): both gates pin to `decl v`, so finality needs `v` in
  `decl v`'s tree and refund needs it absent there.  The abstraction identifies a proof
  with the set fact it proves and has one timeless tree per chain (Specs, model
  boundaries).  For the deployed gates, which read different snapshots through IMT
  proofs, exclusivity further needs the timeout premises (`PROTO-AGGREGATES`,
  `PROTO-BATCH-SNAPSHOT`; `Contracts.Timeout.StaleRootRefundsDeliveredLeg`,
  `AttackVectors.StaleSnapshotBranches.BeginBranchNeedsBeginIsPrevEnd`,
  `AttackVectors.StaleSnapshotBranches.EndBranchNeedsLaterBatchesLate`) and sound IMT
  proofs, and the latter fail at `c67894b9` by the padding forgery
  (`Contracts.InteropCommitmentTree.CThreeLeafWitness`,
  `Contracts.Timeout.PaddingTimeoutLocatesAbsenceBreak`).
* **Check A is NOT redundant at the pin, even under honest insertion.**  Per leg:
  without check A, leg `v` passes the unchecked finality check and passes
  `authorizeRefund` as the missing leg iff it is committed on its real source chain and
  misdeclared, `decl v ≠ srcOf v` (`UncheckedDoubleMintIffMisdeclared`), and the pinned
  `append` reaches such a state (`PinnedMisdeclaredDoubleMint`).  Per flow: without
  check A, a flow passes the finality gate on every leg and `authorizeRefund` on some
  leg (a double mint) iff every leg is live and SOME leg is misdeclared
  (`FlowDoubleMintIffSomeMisdeclared`); the chain running `authorizeRefund` then marks
  every leg it committed under the flow `Revertable`, misdeclared or not.  So the
  reading of `ProofPolarity.inclusion_self_binds` ("the explicit equality check adds
  nothing on this path") and the source comment at `AtomicFlowManager.sol:117-119` are
  false of the pinned contract.
* **The refund pin is to `decl v`, not `srcOf v`.**  A committed leg pinned to its
  declared chain can still have an absence witness (`RefundNotBlockedWhenPinnedToDeclared`);
  a live leg fails `authorizeRefund` as the missing leg, whatever chain the prover names,
  iff `decl v = srcOf v` (`RefundBlockedIffDeclaredIsSource`).  This replaces the reading
  of `ProofPolarity.refund_blocked_when_chain_pinned`, whose premise `c = srcOf v` is not
  the contract's pin.  (A leg that fails as the missing leg is still marked `Revertable`
  when a sibling leg passes `authorizeRefund` on the chain that committed it.)
  **Correction (StaleSnapshotFaithful).**  "Fails `authorizeRefund`" here and in the
  per-leg and per-flow statements is over the set-fact absence check.  At `c67894b9` the
  deployed absence check can also accept a padding forgery when the tree has an empty slot,
  so a live leg declared on its real source chain can still pass `authorizeRefund`
  (`Contracts.Refund.PaddingAcceptedRefundLocatesAbsenceBreak`).
* **Check A is redundant exactly under `DeclaredInsertion`** (`RedundantIffDeclared`;
  the exclusive form is `UncheckedExclusiveUnderDeclared`, whose premises hold together
  by `UncheckedExclusiveUnderDeclaredSatisfiable`), which the upgrade's `append`
  establishes on every honest chain (`UpgradeReachDeclared`, `UpgradeCheckARedundant`).
  In those states `decl v = srcOf v` holds for every committed value
  (`UpgradeExcludesMisdeclared`), so the original model's identification becomes
  accurate there.  Scope: the upgrade results cover histories in which every tree was
  written only by the binding `append` (for example a fresh deployment); values from a
  binding-free `append`, if any chain carries them, are outside them, and check A stays
  load-bearing for flows that use them.

Readings this repair replaces, each now marked "Correction (ProofPolarityFaithful)":
`ProofPolarity`'s header (in its Specs, Properties and Proofs files), its
`inclusion_self_binds`, `refund_blocked_when_chain_pinned` and the section sharpening
the "defense-in-depth" label; `ProofPolarityStrong`'s header and
`unchecked_inclusion_gate_iff_checked`; and the closing section of
`AttackVectors.LocalHonesty` (`Protocol/LocalHonesty.lean`).
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

/-- **BOTH CHECKS TOGETHER ARE EXCLUSIVE, WITH NO HONESTY PREMISE, IN THIS ABSTRACTION.**
With check A and check B both present, no flow is both finalized (every leg proved
against its declared chain) and refunded (some leg proved absent from its declared
chain).  No honesty assumption about any chain is used.

This holds where a proof is the set fact it proves and each chain has one timeless tree
(Specs, model boundaries).  The deployed gates read different snapshots through IMT
proofs, and for them exclusivity further needs the timeout premises
(`PROTO-AGGREGATES`, `PROTO-BATCH-SNAPSHOT`; `Contracts.Timeout.StaleRootRefundsDeliveredLeg`,
`AttackVectors.StaleSnapshotBranches.BeginBranchNeedsBeginIsPrevEnd`,
`AttackVectors.StaleSnapshotBranches.EndBranchNeedsLaterBatchesLate`) and sound IMT
proofs; the latter fail at `c67894b9` by the padding forgery
(`Contracts.InteropCommitmentTree.CThreeLeafWitness`,
`Contracts.Timeout.PaddingTimeoutLocatesAbsenceBreak`). -/
def Properties.CheckedGatesExclusive : Prop :=
  ∀ (Chain Value : Type) (decl : Value → Chain) (tree : Chain → Set Value) (legs : List Value)
    (pc : Value → Chain),
    FlowFinalizedChecked decl tree legs pc → ¬ FlowRefunded decl tree legs

/-- **PER LEG, WITHOUT CHECK A: LEG `v` PASSES THE UNCHECKED FINALITY CHECK AND PASSES
`authorizeRefund` AS THE MISSING LEG IFF IT IS LIVE AND MISDECLARED.**  Under honest
insertion: leg `v` passes the finality check with check A removed at some chain AND
passes `authorizeRefund` as the missing leg at some chain, iff `v` is committed on its
real source chain and its flow declares a different chain.

This is about the two per-leg gates, not about the flow being executed and refunded:
execution needs every leg of the flow finalized, and a passing `authorizeRefund` marks
every leg the running chain committed under the flow `Revertable`.  The flow-level
statement is `FlowDoubleMintIffSomeMisdeclared`.  Absence is the set fact
(Correction (StaleSnapshotFaithful) in the module docstring). -/
def Properties.UncheckedDoubleMintIffMisdeclared : Prop :=
  ∀ (Chain Value : Type) (srcOf decl : Value → Chain) (tree : Chain → Set Value) (v : Value),
    HonestInsertion srcOf tree →
      (((∃ c, FinalityUnchecked tree v c) ∧ ∃ c, RefundChecked decl tree v c)
        ↔ (v ∈ tree (srcOf v) ∧ decl v ≠ srcOf v))

/-- **PER FLOW, WITHOUT CHECK A: THE FLOW IS DOUBLE-MINTED IFF EVERY LEG IS LIVE AND SOME
LEG IS MISDECLARED.**  Under honest insertion: some choice of proof chains passes every
leg of the flow through the finality check with check A removed (`requireFlowFinalized`,
the gate execution calls), and some leg passes `authorizeRefund` as the missing leg (so
the chain running it marks every leg it committed under the flow `Revertable`), iff
every leg is committed on its real source chain and some leg's flow declares a chain
other than its real one.  Absence is the set fact (Correction (StaleSnapshotFaithful) in
the module docstring). -/
def Properties.FlowDoubleMintIffSomeMisdeclared : Prop :=
  ∀ (Chain Value : Type) (srcOf decl : Value → Chain) (tree : Chain → Set Value)
    (legs : List Value),
    HonestInsertion srcOf tree →
      (((∃ pc, FlowFinalizedUnchecked tree legs pc) ∧ FlowRefunded decl tree legs)
        ↔ ((∀ v ∈ legs, v ∈ tree (srcOf v)) ∧ ∃ v ∈ legs, decl v ≠ srcOf v))

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

/-- **A LIVE LEG FAILS `authorizeRefund` AS THE MISSING LEG IFF IT IS DECLARED ON ITS
REAL SOURCE CHAIN.**  Under honest insertion, a leg committed on its real source chain
has no accepted refund proof as the missing leg, for any chain the prover names, iff its
declared chain is its real source chain.  (When it is not, finality is blocked instead,
by check A.)  This is per leg: a leg that fails as the missing leg is still marked
`Revertable` when a sibling leg of its flow passes `authorizeRefund` on the chain that
committed it.

**Correction (StaleSnapshotFaithful).**  Over the set-fact absence check: at `c67894b9` a
padding forgery can pass `authorizeRefund` for a live leg declared on its real source chain
when the tree has an empty slot (`Contracts.Refund.PaddingAcceptedRefundLocatesAbsenceBreak`). -/
def Properties.RefundBlockedIffDeclaredIsSource : Prop :=
  ∀ (Chain Value : Type) (srcOf decl : Value → Chain) (tree : Chain → Set Value) (v : Value),
    HonestInsertion srcOf tree → v ∈ tree (srcOf v) →
      ((¬ ∃ c, RefundChecked decl tree v c) ↔ decl v = srcOf v)

/-- **UNDER `DeclaredInsertion`, CHECK A IS REDUNDANT.**  If every tree holds only legs
declared on its own chain, a flow finalized without check A is finalized with it, and
so is not refunded.  The converse of the first half is `RedundantIffDeclared`. -/
def Properties.UncheckedExclusiveUnderDeclared : Prop :=
  ∀ (Chain Value : Type) (decl : Value → Chain) (tree : Chain → Set Value) (legs : List Value)
    (pc : Value → Chain),
    DeclaredInsertion decl tree → FlowFinalizedUnchecked tree legs pc →
      FlowFinalizedChecked decl tree legs pc ∧ ¬ FlowRefunded decl tree legs

/-- **CHECK A IS REDUNDANT EXACTLY WHERE `DeclaredInsertion` HOLDS.**  In a given state,
every flow finalized without check A is finalized with it (for every leg list and every
choice of proof chains) iff every tree holds only legs declared on its own chain. -/
def Properties.RedundantIffDeclared : Prop :=
  ∀ (Chain Value : Type) (decl : Value → Chain) (tree : Chain → Set Value),
    (∀ (legs : List Value) (pc : Value → Chain),
        FlowFinalizedUnchecked tree legs pc → FlowFinalizedChecked decl tree legs pc)
      ↔ DeclaredInsertion decl tree

/-- **AT THE UPGRADE THE "DEFENSE-IN-DEPTH" READING HOLDS.**  In every state honest
chains reach under the upgraded `append` (from empty trees; `UpgradeReach` gives the
scope), check A adds nothing: a flow finalized without it is finalized with it, and is
not refunded. -/
def Properties.UpgradeCheckARedundant : Prop :=
  ∀ (Chain Value : Type) (srcOf decl : Value → Chain) (tree : Chain → Set Value)
    (legs : List Value) (pc : Value → Chain),
    UpgradeReach srcOf decl tree → FlowFinalizedUnchecked tree legs pc →
      FlowFinalizedChecked decl tree legs pc ∧ ¬ FlowRefunded decl tree legs

/-- **AT THE UPGRADE, DECLARED = REAL ON COMMITTED VALUES.**  In every `UpgradeReach`
state, every committed value's declared chain is its real source chain, which is the
identification `ProofPolarity` makes everywhere. -/
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

/-- **THE PREMISES OF `UncheckedExclusiveUnderDeclared` ARE SATISFIABLE.**  With the leg
declared on its real source chain (`decl = cmSrc`), the state `cmTree` satisfies
`DeclaredInsertion` and the one-leg flow is finalized without check A. -/
def Properties.UncheckedExclusiveUnderDeclaredSatisfiable : Prop :=
  DeclaredInsertion cmSrc cmTree ∧ FlowFinalizedUnchecked cmTree [()] cmSrc

end AttackVectors.ProofPolarityFaithful
