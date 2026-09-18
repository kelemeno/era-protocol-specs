import EraSpec.AttackVectors.BundleStatusMachine
import EraSpec.AttackVectors.AtomicSourceBinding

/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/DestinationCapstone.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  THE DESTINATION-SIDE CAPSTONE.

  `NoTheft.no_theft` is the source side: a leg is committed once, and is delivered or reclaimed but
  never both.  The DESTINATION has its own obligations, and this session proved them separately.  This
  file states them together, which is worth doing for one reason: the hypotheses.  Read apart, each
  result carries its own premises and it is easy to lose track of how many there are and which are
  assumptions about OTHER contracts.  Read together they are four, and two of them are not checkable by
  the destination at all.

  What a delivered bundle gets you, on the atomic path:

    1. each of its calls is delivered AT MOST ONCE                  (bundle-status terminality)
    2. the base-token value released is at most what was collected  (vacuous here -- see below)
    3. the source chain identity shown to recipients is the chain
       whose authenticated tree vouched for the leg                 (inclusion self-binding)
    4. its bundle hash belongs to exactly one send                  (salt guard + encoding injectivity)

  This is a COMPOSITION, not a new argument.  Its content is the hypothesis list at the end, and the
  honest scoping of (2), which is vacuous for atomic bundles because they may not carry native value.
-/

namespace AttackVectors.DestinationCapstone

open AttackVectors.BundleStatusMachine

/-- **DELIVERED-ONCE, ATOMIC PATH.**  An atomic bundle reaches only `Unreceived` or `FullyExecuted`,
and `FullyExecuted` is terminal — so the delivery that writes every call `Executed` happens once, and
the per-call machine is not required on this path. -/
theorem atomic_delivered_once :
    (∀ t : Status, AtomicReach .Unreceived t → t = .Unreceived ∨ t = .FullyExecuted) ∧
      (∀ t : Status, ¬ AtomicStep .FullyExecuted t) ∧
      ¬ AtomicReach .Unreceived .Unbundled :=
  ⟨fun _ h => atomic_reach_two_states h, fun _ => atomic_delivery_terminal, atomic_never_unbundled⟩

/-- **DELIVERED-ONCE, PUBLIC PATH.**  Two routes exist, so both machines are needed: no second entry
into `Executed` within the unbundled route, and no taking both routes. -/
theorem public_delivered_once :
    (∀ t : CallStatus, ¬ CallStep .Executed t) ∧
      (¬ Reach .FullyExecuted .Unbundled ∧ ¬ Reach .Unbundled .FullyExecuted) :=
  value_released_at_most_once

/-- **NO INFLATION**, on the path where it has content.  Restated here so the capstone's second clause
points at the real theorem rather than repeating it. -/
theorem no_inflation (l : Ledger) : releasedSum l ≤ collectedSum l := released_le_collected l

/-! ## The hypotheses, in one place

Everything above is unconditional given the deployed guards.  Clauses 3 and 4 are not, and their
premises are the ones worth carrying away:

**(A) `HonestInsertion` — an assumption about OTHER chains.**  Clause 3 is
`AtomicSourceBinding.atomic_source_bound`, which needs every chain's tree to hold only its own legs'
commit values.  `LocalHonesty` reduces this to "every chain in the leg set runs an unmodified
deployment", enforced locally by a three-link authorisation chain — but the destination cannot verify
it of a foreign chain.  On the atomic path this is the ONLY thing binding the source identity shown to
recipients, since `_validateBundleDestinationContext`'s first check compares the field to itself.

**(B) Keccak injectivity.**  Clause 4 is `BundleHashEncoding.distinct_sends_distinct_hashes`, whose
encoding halves are proved (`abiEncode_inj`, `packed_fixed_inj`) and whose hash halves are assumed, as
everywhere in this corpus.

**(C) Two whole-program enumerations.**  Clause 1's atomic half rests on atomic bundles never reaching
L1 (else the unbundled route opens for them); clause 2's release path rests on `give` and
`_handleCallValue` having one call site each.  Neither is a guard; both are checked by
`scripts/check-source-invariants.sh`.

**(D) Nothing here covers the SOURCE side.**  Whether the value was actually burned on the origin
chain, and whether a timed-out leg can be recovered, are `NoTheft` and `RecoveryLimits` respectively —
and the latter records that recovery is partial.  A reader wanting "no theft, end to end" needs all
three files, not this one.

## What is deliberately NOT claimed

* Clause 2 is VACUOUS for atomic bundles (`atomic_ledger_trivial`): they may not carry native value, so
  both sums are zero.  It has content only on the public path.
* Nothing says a CANCELLED call's collected value is recoverable.  It is not released at the
  destination, and this corpus does not follow it back to the source.
* Nothing here is a liveness claim.  `BundleStatusMachine` records that `executeAtomicBundle` admits
  only `Unreceived`, and `RecoveryLimits` that a single reverting target blocks a whole refund. -/

end AttackVectors.DestinationCapstone
