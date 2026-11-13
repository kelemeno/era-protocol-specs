import EraSpec.Contracts.InteropHandlerBase.Specs.SelfCallAuthority

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false


/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/SelfCallAuthority.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  THE `msg.sender == address(this)` DISJUNCT — when a self-call is not an authority bypass.

  Three permission gates in the handler open for the contract itself:

      executeBundle       msg.sender == address(this) || (executionChainId matches && executionAddress == msg.sender)
      unbundleBundle      msg.sender == address(this) || (unbundlerChainId matches && unbundlerAddress == msg.sender)
      executeAtomicBundle msg.sender == address(this) || (executionChainId matches && executionAddress == msg.sender)

  Read alone, `msg.sender == address(this)` is an unconditional bypass.  It is safe because of a
  DELEGATION pattern the docstring states:

      "Since this function validates permissions, the called functions (executeBundle/unbundleBundle)
       will bypass their own permission checks when called from this contract."

  `receiveMessage` is the only entry that produces a self-call: it requires `msg.sender ==
  address(this)` itself (so it fires only when a bundle's call targets the handler), parses the
  ORIGINAL message's `(senderChainId, senderAddress)`, checks the attribute against THOSE, and only
  then makes the self-call.

  The pattern is sound exactly when every self-call site is preceded by the matching check.  That is an
  ENUMERATION, not a guard.  The statements of THIS file do not capture what the enumeration buys (see
  `selfCall_relays_authority`); topic `SelfCallAuthorityStrong` does, as a theorem over every
  dispatch table.  `scripts/check-source-invariants.sh`, a script of the sibling
  contracts-formal-verification repository (not of this package), tests that the enumeration still
  holds.  Verified at the time of writing:

      InteropHandlerBase.sol:391   this.executeBundle     preceded by the executionAddress check
      InteropHandlerBase.sol:401   this.verifyBundle      permissionless by design, no check needed
      InteropHandlerBase.sol:425   this.unbundleBundle    preceded by the unbundlerAddress check

  and `receiveMessage` dispatches on exactly three selectors, one per site.
-/

namespace AttackVectors.SelfCallAuthority


/-- **AS STATED, THIS ONLY REPACKAGES ITS PREMISE.**  The conclusion `∃ ch addr, attrAllows a ch ch
addr` holds for every attribute — `none` allows everyone, and `some (ch, addr)` allows `(ch, addr)`
itself — so `checked` is not used, and the statement mentions neither the inner gate, nor the
self-call, nor the original sender.  It does not establish the delegation claim it is named after (a
gate passing via its self-call disjunct had the attribute checked against the ORIGINAL sender, one
frame up).  That claim is topic `SelfCallAuthorityStrong`:
`DeployedSelfCallRelaysOriginalSenderAuthority` for the deployed dispatch, and
`SelfCallRelaySoundIffEveryGatedBranchChecked` for every dispatch table. -/
abbrev Properties.selfCall_relays_authority {a : Attr} {thisChain senderChain senderAddr : ℕ}
    (checked : attrAllows a senderChain senderChain senderAddr) :=
  ∃ ch addr, attrAllows a ch ch addr


/-- **AND AN UNCHECKED SELF-CALL SITE WOULD WIDEN IT.**  The disjunct passes on `isSelf` alone,
whatever the attribute says — so a self-call added without the preceding check hands the gated action
to anyone who can get a bundle executed.  This is why the enumeration, not the gate, is what makes the
pattern safe.  (A fact about `innerGate` alone; with the dispatch table modelled, the same widening
is `SelfCallAuthorityStrong.UncheckedAtomicBranchWidensAuthority`.) -/
abbrev Properties.unchecked_selfCall_widens_authority :=
  ∃ (a : Attr) (thisChain callerChain callerAddr : ℕ),
        innerGate a thisChain callerChain callerAddr True ∧
          ¬ attrAllows a thisChain callerChain callerAddr


/-- The permissionless case needs no relay: an absent attribute allows everyone, so
`this.verifyBundle` is safe without a preceding check. -/
abbrev Properties.absent_attr_permissionless {thisChain callerChain callerAddr : ℕ} :=
  attrAllows none thisChain callerChain callerAddr


/-! ## An inert disjunct, worth knowing about

`executeAtomicBundle` carries the same `msg.sender == address(this)` disjunct, but `receiveMessage`
dispatches on only three selectors — `executeBundle`, `verifyBundle`, `unbundleBundle` — and no other
self-call site exists.  So NOTHING currently reaches `executeAtomicBundle` as a self-call, and that
disjunct is dead code today.

It is harmless while it stays dead, and defensible as symmetry with `executeBundle`.  The thing to
notice is what would change it: adding a fourth selector branch for atomic execution would make the
disjunct live in the same commit, and it would be live BEFORE anyone wrote the corresponding
`_handleExecuteAtomicBundle` permission check — the check being in a different function from the
disjunct it protects.  That is the ordering that turns this pattern into a bypass, so it is recorded
here and counted by the script. -/

end AttackVectors.SelfCallAuthority
