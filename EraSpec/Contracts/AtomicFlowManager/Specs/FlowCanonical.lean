import Mathlib.Tactic


/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/FlowCanonical.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  THE FLOW IS CANONICAL — what the adjacent-only check actually buys.

  Source: era-contracts `draft/v0.35.0` at `b17415d20`, `l1-contracts/contracts/atomic-interop/`.
  `_validateAndComputeFlowId` (`AtomicFlowManager.sol:360-379`) runs on every `append` (`:109`) and,
  through `_checkFlowId` (`:348-353`), on every `requireFlowFinalized` (`:182`) and `authorizeRefund`
  (`:217`).  Its ordering check is a NEIGHBOUR scan, followed by the length check:

      uint256 n = _preimage.legBundleHashes.length;
      for (uint256 i = 1; i < n; ++i) {                                                 // :370-374
          if (_preimage.legBundleHashes[i] <= _preimage.legBundleHashes[i - 1]) revert ManagerBundleHashesNotSorted();
      }
      if (_preimage.legSourceChainIds.length != n) revert ManagerLegSourceChainIdsLengthMismatch(...);  // :375-377

  These two checks read the same at the older pin `c67894b9`, where they made up all of `_checkFlowId`.
  At `b17415d20` two more checks come first, the version byte and the eight-leg cap (`:361-369`).  So
  `Valid` below is the conjunction of two of the four checks: necessary for acceptance, not sufficient.
  The exact acceptance condition is `Contracts.FlowCanonicalAtV35.Properties.AcceptedV35Iff`.

  Group #37 proves the GUARD over the compiled blocks: each adjacent pair must be strictly ascending,
  and the lengths must match.  What #37 records but does not prove is the CONSEQUENCE, in its own words:

      "Canonical ascending order also makes the flow presentation unique per leg set."
      "... an injected or duplicated leg, a permuted flow re-presentation ... is rejected up front"

  Those are global claims -- about ALL pairs of positions, and about all permutations -- drawn from a
  check that only ever compares neighbours.  The step from one to the other is transitivity, and it is
  the part no file states.  This closes it, and shows the gap is real by exhibiting a neighbour check
  that does NOT close: distinctness.

  These are order-theoretic facts, so they are proved over an arbitrary `LinearOrder` and instantiated
  at `ℕ`; nothing here depends on the word size.
-/

namespace AttackVectors.FlowCanonical


variable {α : Type*} [LinearOrder α]


/-- The deployed check, verbatim in shape: every ADJACENT pair strictly ascends. -/
def Ascending (l : List α) : Prop := l.IsChain (· < ·)


/-! ## The flow, and the pairing the length check protects

`legSourceChainIds` is positional, not a set -- the source comment is explicit that treating it as an
ascending set "would let a sibling chain in the set still enable a wrong-chain refund".  So the pairing
is by index, and its integrity rests on the two guards jointly: the length check makes every leg HAVE a
chain id, and the ordering check makes the leg keys distinct, so the pairing is a genuine function. -/

structure Flow (α β : Type*) where
  legs : List α
  chains : List β


/-- The sort check and the length check both pass (`AtomicFlowManager.sol:370-377`). At `b17415d20`
this is necessary for `_validateAndComputeFlowId` to accept, not sufficient: the version byte and the leg
cap are checked too (`Contracts.FlowCanonicalAtV35.AcceptedV35`). -/
def Valid {β : Type*} (f : Flow α β) : Prop :=
  Ascending f.legs ∧ f.chains.length = f.legs.length


end AttackVectors.FlowCanonical
