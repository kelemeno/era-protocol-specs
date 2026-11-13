import EraSpec.Contracts.AtomicFlowManager.Specs.RecoveryLimits

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false


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
       (`AtomicFlowManager.sol:172`), which is terminal.  On the manager's runs that is
       `Contracts.AtomicFlowManager.no_double_claim`; `refunded_leg_cannot_refund_again` is the
       sibling repository's name, not a theorem here.  So the declining calls' funds are stranded
       PERMANENTLY, by a transaction that reported success.  The statements below record the two
       halves separately.  Tied together on the real loop and the manager's runs, they are
       `Contracts.AtomicFlowManager.RecoveryLimitsStrong.Properties.partial_stranding_is_terminal`
       (`Properties/RecoveryLimitsStrong.lean`; `RecoveryLimitsStrong` below means that namespace).

    2. The call is raw — no `try/catch`.  A target that REVERTS rather than returning `false` aborts
       the whole claim, including the calls that would have recovered.  Retrying re-enters the same
       loop and hits the same target, so recovery stays unavailable while any target reverts.  The
       outcome lists below are fixed, so that retry argument is not formalized here.  Over a world
       that changes between attempts it is `RecoveryLimitsStrong.Properties.blocked_retry_reverts`
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


/-! ## Limit 1 — a successful claim can strand funds permanently -/

/-- **PARTIAL RECOVERY IS ACCEPTED.**  One recovering call carries a bundle of any size: the claim
succeeds with every other call left unrecovered. -/
abbrev Properties.partial_recovery_accepted :=
  ClaimAccepted [Outcome.recovered, Outcome.declined, Outcome.declined]


/-- The threshold is not "all": a bundle can be accepted with strictly fewer recoveries than calls. -/
abbrev Properties.accepted_below_full_recovery :=
  ∃ os : List Outcome, ClaimAccepted os ∧ recoveredCount os < os.length


/-- **A `Reverted` LEG IS NOT CLAIM-ENABLED.**  A constructor fact on this file's own copy of `LegState`
(`Reverted ≠ Revertable`).  It involves no run and no tie to the manager's state.
`AtomicFlowManager.Layout.refunded_leg_cannot_refund_again` is in the sibling repository, not here.
Terminality on the manager's runs is `Contracts.AtomicFlowManager.no_double_claim`.  Tied to the claim the
recovery loop accepted, it is
`Contracts.AtomicFlowManager.RecoveryLimitsStrong.Properties.legClaim_success_closes_leg`.  The copy is the
manager's state renamed (`RecoveryLimitsStrong.Properties.leg_copy_is_model_leg`). -/
abbrev Properties.no_second_claim :=
  ¬ claimEnabled afterClaim


/-- **PARTIAL ACCEPTANCE, AND A CLOSED GATE.**  Some outcome list is accepted with strictly fewer
recoveries than calls, and `afterClaim` does not enable a claim.  The last conjunct does not mention `os`,
because `afterClaim` is a constant.  So this is exactly `accepted_below_full_recovery` together with
`no_second_claim`, and it does not tie the closed gate to the claim that was accepted, or to any run.  The
tied statement is `Contracts.AtomicFlowManager.RecoveryLimitsStrong.Properties.partial_stranding_is_terminal`.
There, the real loop
accepts a claim with fewer recoveries than calls, on a leg reached from fresh storage.  From the state that
claim leaves, no run of the manager lets any claim of that leg succeed.  So the unrecovered calls get no
second attempt, and Limit 1 is not a retry away from being fixed. -/
abbrev Properties.stranding_is_terminal :=
  ∃ os : List Outcome,
        ClaimAccepted os ∧ recoveredCount os < os.length ∧ ¬ claimEnabled afterClaim


/-! ## Limit 2 — one reverting target denies recovery to every other call

This is the fact that does not fit "the flow author's responsibility": the loss is not confined to the
offending call. -/

/-- **A SINGLE REVERTING TARGET BLOCKS THE WHOLE CLAIM**, including calls that would have recovered. -/
abbrev Properties.one_revert_blocks_all :=
  ¬ ClaimAccepted [Outcome.recovered, Outcome.reverts, Outcome.recovered]


/-- Sharper: for ANY list of otherwise-recovering calls, inserting one reverting target denies the
claim.  So the coupling is not an artefact of the example above. -/
abbrev Properties.revert_anywhere_blocks (pre post : List Outcome) :=
  ¬ ClaimAccepted (pre ++ Outcome.reverts :: post)


/-- **A LOOP THAT HITS A REVERT IS NOT ACCEPTED.**  The conclusion restates the premise:
`¬ LoopCompletes os` denies the first conjunct of `ClaimAccepted os`, so this adds nothing to
`revert_anywhere_blocks`.  No retry is modelled.  The outcome list is fixed, so a second attempt against
targets whose state has changed is not covered here.  That version is
`Contracts.AtomicFlowManager.RecoveryLimitsStrong.Properties.blocked_retry_reverts`: if some call reverts in
every world that keeps a
stated invariant, then every retry reverts in every later world that keeps it.
`RecoveryLimitsStrong.Properties.blocked_leg_stays_revertable` adds that the leg stays `Revertable` along
every run in which the world changes and other legs move.  Without that condition, "fails identically" is
false: `RecoveryLimitsStrong.Properties.retry_succeeds_once_blocker_clears` is a claim that reverts and
then succeeds once the blocking target's state changes. -/
abbrev Properties.retry_does_not_help (os : List Outcome) (h : ¬ LoopCompletes os) :=
  ¬ ClaimAccepted os


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
abbrev Properties.validation_unbypassable {Bundle : Type*} (Validated Committed : Bundle → Prop)
    (sole_path : ∀ b, Committed b → Validated b) {b : Bundle} (h : Committed b) :=
  Validated b


end AttackVectors.RecoveryLimits
