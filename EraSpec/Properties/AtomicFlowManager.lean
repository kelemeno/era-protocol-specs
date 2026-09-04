import EraSpec.Contracts.AtomicFlowManager

/-!
# Properties: the flow manager

Statements about the per-leg state machine in
`EraSpec.Contracts.AtomicFlowManager`.  Proofs are in
`EraSpec.Proofs.AtomicFlowManager`; every property below has a certificate there.

Everything here follows from one fact — the three operations only move a leg up
`Unset → Committed → Revertable → Reverted` — so the first two properties are the
engine and the rest are its consequences.
-/

namespace Properties.AtomicFlowManager

open Contracts.AtomicFlowManager

/-! ## The rank is monotone -/

/-- No leg ever moves backward: one step cannot lower any leg's rank.  Stated
for EVERY leg, not just the one the step touches, so it composes over runs. -/
def StepRankMono : Prop :=
  ∀ (M N : Manager), Step M N → ∀ (f b : UInt256), rank (M.legState f b) ≤ rank (N.legState f b)

/-- Monotonicity along whole runs. -/
def ReachRankMono : Prop :=
  ∀ (M N : Manager), Reach M N → ∀ (f b : UInt256), rank (M.legState f b) ≤ rank (N.legState f b)

/-! ## Consequences -/

/-- `Reverted` is absorbing: a refunded leg stays refunded through any run.  The
no-double-refund guarantee in its strongest form. -/
def RevertedAbsorbing : Prop :=
  ∀ (M N : Manager), Reach M N → ∀ (f b : UInt256),
    M.legState f b = .Reverted → N.legState f b = .Reverted

/-- A leg cannot be claimed twice: after a claim, no reachable state admits
`ClaimGuard` for that leg. -/
def NoDoubleClaim : Prop :=
  ∀ (M N : Manager) (f b : UInt256),
    ClaimGuard M f b → Reach (M.set f b .Reverted) N → ¬ ClaimGuard N f b

/-- A refund requires a prior authorization: if the claim gate is open, the leg's
rank is already 2, which only `authorize` produces. -/
def ClaimRequiresAuthorization : Prop :=
  ∀ (M : Manager) (f b : UInt256), ClaimGuard M f b → rank (M.legState f b) = 2

/-- A leg with no commitment on this chain cannot be refunded here. -/
def UnsetNotClaimable : Prop :=
  ∀ (M : Manager) (f b : UInt256), M.legState f b = .Unset → ¬ ClaimGuard M f b

/-- `claimRefund` cannot be reached from `Committed` without `authorizeRefund`,
which is where the timeout proof is checked. -/
def CommittedNotClaimable : Prop :=
  ∀ (M : Manager) (f b : UInt256), M.legState f b = .Committed → ¬ ClaimGuard M f b

/-- Append is once per leg: after a commit, no reachable state admits
`AppendGuard` for it — so a leg's commit value enters the tree at most once. -/
def NoDoubleAppend : Prop :=
  ∀ (M N : Manager) (f b : UInt256),
    AppendGuard M f b → Reach (M.set f b .Committed) N → ¬ AppendGuard N f b

/-- The CEI order is what removes the need for a reentrancy guard: in the state
the external recovery calls run against, the leg is already `Reverted`, so the
claim gate is closed for their whole duration. -/
def ClaimClosesGateBeforeInteraction : Prop :=
  ∀ (M : Manager) (f b : UInt256), ¬ ClaimGuard (M.set f b .Reverted) f b

/-- The lifecycle is exactly four states deep. -/
def RankLeThree : Prop :=
  ∀ (M : Manager) (f b : UInt256), rank (M.legState f b) ≤ 3

end Properties.AtomicFlowManager
