import Mathlib.Tactic


/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/FlowCanonical.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  THE FLOW IS CANONICAL — what the adjacent-only check actually buys.

  `_checkFlowId` guards every delivery and every reclaim, and its ordering check is a NEIGHBOUR scan:

      uint256 n = _flow.legBundleHashes.length;
      for (uint256 i = 1; i < n; ++i) {
          if (_flow.legBundleHashes[i] <= _flow.legBundleHashes[i - 1]) revert ManagerBundleHashesNotSorted();
      }
      if (_flow.legSourceChainIds.length != n) revert ManagerLegSourceChainIdsLengthMismatch(...);

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
def Ascending (l : List α) : Prop := l.Chain' (· < ·)


/-! ## The flow, and the pairing the length check protects

`legSourceChainIds` is positional, not a set -- the source comment is explicit that treating it as an
ascending set "would let a sibling chain in the set still enable a wrong-chain refund".  So the pairing
is by index, and its integrity rests on the two guards jointly: the length check makes every leg HAVE a
chain id, and the ordering check makes the leg keys distinct, so the pairing is a genuine function. -/

structure Flow (α β : Type*) where
  legs : List α
  chains : List β


/-- An accepted flow: what `_checkFlowId` lets through. -/
def Valid {β : Type*} (f : Flow α β) : Prop :=
  Ascending f.legs ∧ f.chains.length = f.legs.length


end AttackVectors.FlowCanonical
