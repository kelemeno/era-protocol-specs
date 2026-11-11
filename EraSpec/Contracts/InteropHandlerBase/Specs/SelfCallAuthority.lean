import Mathlib.Tactic


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
  ENUMERATION, not a guard, so this file states what the enumeration buys and
  `scripts/check-source-invariants.sh` tests that it still holds.  Verified at the time of writing:

      InteropHandlerBase.sol:391   this.executeBundle     preceded by the executionAddress check
      InteropHandlerBase.sol:401   this.verifyBundle      permissionless by design, no check needed
      InteropHandlerBase.sol:425   this.unbundleBundle    preceded by the unbundlerAddress check

  and `receiveMessage` dispatches on exactly three selectors, one per site.
-/

namespace AttackVectors.SelfCallAuthority


/-- An attribute naming who may act: a chain and an address, or absent (permissionless). -/
abbrev Attr := Option (ℕ × ℕ)


/-- The attribute check, parameterised by the chain it is compared against.  The two paths differ only
in that chain: the DIRECT path compares to `block.chainid`, the cross-chain path to the message's
sender chain.  `chainId == 0` is the chain-agnostic wildcard in both. -/
def attrAllows (a : Attr) (againstChain callerChain callerAddr : ℕ) : Prop :=
  match a with
  | none => True
  | some (ch, addr) => (ch = againstChain ∨ ch = 0) ∧ addr = callerAddr ∧ againstChain = callerChain


/-- The inner gate: self-call, or the attribute allows the direct caller. -/
def innerGate (a : Attr) (thisChain callerChain callerAddr : ℕ) (isSelf : Prop) : Prop :=
  isSelf ∨ attrAllows a thisChain callerChain callerAddr


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
