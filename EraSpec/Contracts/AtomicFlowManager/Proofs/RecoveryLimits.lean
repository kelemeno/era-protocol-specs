import EraSpec.Contracts.AtomicFlowManager.Properties.RecoveryLimits
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
       (`AtomicFlowManager.sol:172`), which is terminal.  On the manager's runs that is
       `Contracts.AtomicFlowManager.no_double_claim`; `refunded_leg_cannot_refund_again` is the
       sibling repository's name, not a theorem here.  So the declining calls' funds are stranded
       PERMANENTLY, by a transaction that reported success.  Tied together on the real loop and the
       manager's runs, the two halves are
       `Contracts.AtomicFlowManager.RecoveryLimitsStrong.partial_stranding_is_terminal`.

    2. The call is raw — no `try/catch`.  A target that REVERTS rather than returning `false` aborts
       the whole claim, including the calls that would have recovered.  Retrying re-enters the same
       loop and hits the same target, so recovery stays unavailable while any target reverts.  The
       outcome lists here are fixed, so that retry argument is not proved in this file.  Over a world
       that changes between attempts it is
       `Contracts.AtomicFlowManager.RecoveryLimitsStrong.blocked_retry_reverts`.

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
theorem partial_recovery_accepted :
    Properties.partial_recovery_accepted := by
  unfold Properties.partial_recovery_accepted
  exact
    by
      constructor
      · decide
      · decide


/-- The threshold is not "all": a bundle can be accepted with strictly fewer recoveries than calls. -/
theorem accepted_below_full_recovery :
    Properties.accepted_below_full_recovery := by
  unfold Properties.accepted_below_full_recovery
  exact
    by
      refine ⟨[Outcome.recovered, Outcome.declined, Outcome.declined], ⟨by decide, by decide⟩, by decide⟩


/-- **A `Reverted` LEG IS NOT CLAIM-ENABLED.**  A constructor fact on this file's copy of `LegState`.
Terminality on the manager's runs is `Contracts.AtomicFlowManager.no_double_claim`; tied to an accepted
claim it is `Contracts.AtomicFlowManager.RecoveryLimitsStrong.legClaim_success_closes_leg`. -/
theorem no_second_claim :
    Properties.no_second_claim := by
  unfold Properties.no_second_claim
  exact
    by decide


/-- **PARTIAL ACCEPTANCE, AND A CLOSED GATE.**  `accepted_below_full_recovery` together with
`no_second_claim`; the closed gate is a constant fact, not tied to the accepted claim.  The tied statement,
on the real loop and the manager's runs, is
`Contracts.AtomicFlowManager.RecoveryLimitsStrong.partial_stranding_is_terminal`. -/
theorem stranding_is_terminal :
    Properties.stranding_is_terminal := by
  unfold Properties.stranding_is_terminal
  exact
    by
      refine ⟨[Outcome.recovered, Outcome.declined, Outcome.declined],
        ⟨by decide, by decide⟩, by decide, no_second_claim⟩


/-! ## Limit 2 — one reverting target denies recovery to every other call

This is the fact that does not fit "the flow author's responsibility": the loss is not confined to the
offending call. -/

/-- **A SINGLE REVERTING TARGET BLOCKS THE WHOLE CLAIM**, including calls that would have recovered. -/
theorem one_revert_blocks_all :
    Properties.one_revert_blocks_all := by
  unfold Properties.one_revert_blocks_all
  exact
    by
      rintro ⟨hloop, -⟩
      exact hloop (by decide)


/-- Sharper: for ANY list of otherwise-recovering calls, inserting one reverting target denies the
claim.  So the coupling is not an artefact of the example above. -/
theorem revert_anywhere_blocks (pre post : List Outcome) :
    Properties.revert_anywhere_blocks (pre := pre) (post := post) := by
  unfold Properties.revert_anywhere_blocks
  exact
    by
      rintro ⟨hloop, -⟩
      exact hloop (List.mem_append.mpr (Or.inr List.mem_cons_self))


/-- **A LOOP THAT HITS A REVERT IS NOT ACCEPTED.**  This restates the premise; no retry is modelled.
The retry statement over a changing world is
`Contracts.AtomicFlowManager.RecoveryLimitsStrong.blocked_retry_reverts`, and
`retry_succeeds_once_blocker_clears` there shows it needs its invariant premises. -/
theorem retry_does_not_help (os : List Outcome) (h : ¬ LoopCompletes os) :
    Properties.retry_does_not_help (os := os) (h := h) := by
  unfold Properties.retry_does_not_help
  exact
    fun hacc => h hacc.1


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
    (sole_path : ∀ b, Committed b → Validated b) {b : Bundle} (h : Committed b) :
    Properties.validation_unbypassable (Bundle := Bundle) (Validated := Validated) (Committed := Committed) (sole_path := sole_path) (b := b) (h := h) := by
  unfold Properties.validation_unbypassable
  exact
    sole_path b h


end AttackVectors.RecoveryLimits
