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
       (`AtomicFlowManager.sol:172`), which `refunded_leg_cannot_refund_again` shows is terminal.  So
       the declining calls' funds are stranded PERMANENTLY, by a transaction that reported success.

    2. The call is raw — no `try/catch`.  A target that REVERTS rather than returning `false` aborts
       the whole claim, including the calls that would have recovered.  Retrying re-enters the same
       loop and hits the same target, so recovery stays unavailable while any target reverts.

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

/-! ## Limit 1 — a successful claim can strand funds permanently -/

/-- **PARTIAL RECOVERY IS ACCEPTED.**  One recovering call carries a bundle of any size: the claim
succeeds with every other call left unrecovered. -/
theorem partial_recovery_accepted :
    ClaimAccepted [Outcome.recovered, Outcome.declined, Outcome.declined] := by
  constructor
  · decide
  · decide

/-- The threshold is not "all": a bundle can be accepted with strictly fewer recoveries than calls. -/
theorem accepted_below_full_recovery :
    ∃ os : List Outcome, ClaimAccepted os ∧ recoveredCount os < os.length := by
  refine ⟨[Outcome.recovered, Outcome.declined, Outcome.declined], ⟨by decide, by decide⟩, by decide⟩

/-- The leg's state machine, as `AtomicFlowManager` writes it. -/
inductive LegState
  | Unset | Committed | Revertable | Reverted
  deriving DecidableEq, Repr

/-- `claimRefund` is enabled only on a `Revertable` leg. -/
abbrev claimEnabled (s : LegState) : Prop := s = LegState.Revertable

/-- It sets `Reverted` BEFORE the external calls (`AtomicFlowManager.sol:172`), so a reentrant or
later claim sees the post-state. -/
abbrev afterClaim : LegState := LegState.Reverted

/-- **AND IT IS TERMINAL.**  A `Reverted` leg does not enable another claim — the concrete counterpart
is `AtomicFlowManager.Layout.refunded_leg_cannot_refund_again`. -/
theorem no_second_claim : ¬ claimEnabled afterClaim := by decide

/-- **SO PARTIAL STRANDING IS PERMANENT.**  A claim can be accepted while strictly fewer calls recover
than the bundle contains, and that acceptance closes the only door: the unrecovered calls get no second
attempt.  Limit 1 is not a retry away from being fixed. -/
theorem stranding_is_terminal :
    ∃ os : List Outcome,
      ClaimAccepted os ∧ recoveredCount os < os.length ∧ ¬ claimEnabled afterClaim := by
  refine ⟨[Outcome.recovered, Outcome.declined, Outcome.declined],
    ⟨by decide, by decide⟩, by decide, no_second_claim⟩

/-! ## Limit 2 — one reverting target denies recovery to every other call

This is the fact that does not fit "the flow author's responsibility": the loss is not confined to the
offending call. -/

/-- **A SINGLE REVERTING TARGET BLOCKS THE WHOLE CLAIM**, including calls that would have recovered. -/
theorem one_revert_blocks_all :
    ¬ ClaimAccepted [Outcome.recovered, Outcome.reverts, Outcome.recovered] := by
  rintro ⟨hloop, -⟩
  exact hloop (by decide)

/-- Sharper: for ANY list of otherwise-recovering calls, inserting one reverting target denies the
claim.  So the coupling is not an artefact of the example above. -/
theorem revert_anywhere_blocks (pre post : List Outcome) :
    ¬ ClaimAccepted (pre ++ Outcome.reverts :: post) := by
  rintro ⟨hloop, -⟩
  exact hloop (List.mem_append.mpr (Or.inr (List.mem_cons_self _ _)))

/-- And retrying does not help: the condition depends only on the outcomes, so a second attempt against
the same targets fails identically.  Recovery is unavailable for as long as any target reverts. -/
theorem retry_does_not_help (os : List Outcome) (h : ¬ LoopCompletes os) :
    ¬ ClaimAccepted os := fun hacc => h hacc.1

/-! ## What IS unconditional: the native-`value` rejection

`_validateAtomicBundle` rejects any call carrying native `value`, because no `recoverAtomicCall` can
reverse a base-token transfer.  Unlike the two limits above this guard cannot be evaded, and the reason
is the same single-funnel structure `LocalHonesty` established:

    InteropCenter.sol:574   the sole `_dispatchBundle` call site
    InteropCenter.sol:646   `if (_atomicSend.isAtomic) {`
    InteropCenter.sol:649       `_validateAtomicBundle(_bundle);`
    InteropCenter.sol:650       `... .append({_bundleHash: bundleHash, ...})`

`append` has one call site, `_dispatchBundle` has one call site, and the validation precedes the append
inside the same branch — so every committed atomic leg was validated.  The claim in the source comment
("Every atomic send passes through {_dispatchBundle}, so this covers all atomic bundles regardless of
entry path") is therefore accurate, and rests on the same enumeration `LocalHonesty.sole_call_site`
does. -/

/-- The funnel, abstracted: validation that precedes the only commit path covers every commit. -/
theorem validation_unbypassable {Bundle : Type*} (Validated Committed : Bundle → Prop)
    (sole_path : ∀ b, Committed b → Validated b) {b : Bundle} (h : Committed b) : Validated b :=
  sole_path b h

end AttackVectors.RecoveryLimits
