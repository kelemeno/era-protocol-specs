import Mathlib.Tactic


/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/RecoveryLimits.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  TIMEOUT RECOVERY — the exact shape of "best-effort".

  The source is candid that refund recovery is partial:

      "timeout recovery is best-effort (see {AtomicFlowManager._recoverBundle})"
      "Refund safety for a fund-moving leg is therefore the flow author's responsibility; only
       native-`value` legs — which no one can reverse — are blocked here."

  So the LIMIT is acknowledged.  What is not stated anywhere is its exact shape, and the loop is short
  enough to read off precisely:

      for (uint256 i = 0; i < callsLen; ++i) {
          InteropCall memory c = _bundle.calls[i];
          if (IAtomicRecoverable(c.to).recoverAtomicCall(destChainId, c.data)) { ++recovered; }
      }
      if (recovered == 0) revert ManagerNoRecoverableCalls(_flowId, _bundleHash);

  Two facts follow that "best-effort" does not convey:

    1. The acceptance threshold is `recovered >= 1`, NOT `recovered == callsLen`.  A claim in which one
       call recovers and the rest decline SUCCEEDS, and `claimRefund` marks the leg `Reverted` first
       (`AtomicFlowManager.sol:175`), which is terminal.  On the manager's runs that is
       `Contracts.AtomicFlowManager.no_double_claim`; `refunded_leg_cannot_refund_again` is the
       sibling repository's name, not a theorem here.  So the declining calls' funds are stranded
       PERMANENTLY, by a transaction that reported success.  The properties file records the two
       halves separately.  Tied together on the real loop and the manager's runs, they are
       `Contracts.AtomicFlowManager.RecoveryLimitsStrong.Properties.partial_stranding_is_terminal`
       (`Properties/RecoveryLimitsStrong.lean`; `RecoveryLimitsStrong` below means that namespace).

    2. The call is raw — no `try/catch`.  A target that REVERTS rather than returning `false` aborts
       the whole claim, including the calls that would have recovered.  Retrying re-enters the same
       loop and hits the same target, so recovery stays unavailable while any target reverts.  The
       outcome lists here are fixed, so that retry argument is not formalized in this file.  Over a
       world that changes between attempts it is `RecoveryLimitsStrong.Properties.blocked_retry_reverts`
       and `blocked_leg_stays_revertable`.

  Fact 2 is the one that does not fit the docstring's framing.  "The flow author's responsibility" is a
  per-call statement, but a reverting target denies recovery to the OTHER calls too — the failure
  couples calls that the comment treats as independent, and the author may not control every target.

  This file records both as LIMITS, in the manner of `FlowAtomicity.mixed_outcomes_permitted`.  Nothing
  here says the system is unsafe: it says what a successful `claimRefund` does and does not promise, so
  the promise is not overread.  What IS unconditionally enforced is the native-`value` rejection, and
  that is proved unbypassable at the end.
-/

namespace AttackVectors.RecoveryLimits


/-- What one call's `recoverAtomicCall` does. -/
inductive Outcome
  | recovered   -- returned true
  | declined    -- returned false
  | reverts     -- threw; no `try/catch`, so the whole claim aborts
  deriving DecidableEq, Repr


/-- The loop aborts if ANY target reverts. -/
abbrev LoopCompletes (os : List Outcome) : Prop := Outcome.reverts ∉ os


/-- `recovered` at the end of the loop. -/
def recoveredCount (os : List Outcome) : ℕ := (os.filter (· = Outcome.recovered)).length


/-- The deployed acceptance condition: the loop ran to completion and at least one call recovered. -/
abbrev ClaimAccepted (os : List Outcome) : Prop := LoopCompletes os ∧ recoveredCount os ≠ 0


/-- The leg's state machine, as `AtomicFlowManager` writes it. -/
inductive LegState
  | Unset | Committed | Revertable | Reverted
  deriving DecidableEq, Repr


/-- `claimRefund` is enabled only on a `Revertable` leg. -/
abbrev claimEnabled (s : LegState) : Prop := s = LegState.Revertable


/-- It sets `Reverted` BEFORE the external calls (`AtomicFlowManager.sol:175`), so a reentrant or
later claim sees the post-state.  This file only names that post-state.  The constant proves neither
consequence.  The reentrant case is
`Contracts.AtomicFlowManager.ModelStrong.Properties.writeFirst_callback_never_reclaims`.  The later-claim
case on the manager's runs is
`Contracts.AtomicFlowManager.RecoveryLimitsStrong.Properties.legClaim_success_closes_leg`. -/
abbrev afterClaim : LegState := LegState.Reverted


end AttackVectors.RecoveryLimits
