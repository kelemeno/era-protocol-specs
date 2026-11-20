import EraSpec.Contracts.AtomicFlowManager.Specs.FlowCanonical

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false


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


/-- **NEIGHBOURS GIVE ALL PAIRS.**  The bridge from the loop to the global claims: because `<` is
transitive, scanning adjacent pairs pins every pair of positions. -/
abbrev Properties.ascending_iff_pairwise {l : List α} :=
  Ascending l ↔ l.Pairwise (· < ·)


/-- Strictly ascending at every earlier/later position pair. -/
abbrev Properties.ascending_lt_of_lt {l : List α} (h : Ascending l) {i j : Fin l.length} (hij : i < j) :=
  l.get i < l.get j


/-- **NO DUPLICATED LEG.**  Distinct positions carry distinct bundle hashes -- so a flow cannot list
the same leg twice, at any distance.  The loop never compares position 0 with position 5; this is why
it does not have to. -/
abbrev Properties.no_duplicate_leg {l : List α} (h : Ascending l) {i j : Fin l.length} (hne : i ≠ j) :=
  l.get i ≠ l.get j


abbrev Properties.ascending_nodup {l : List α} (h : Ascending l) :=
  l.Nodup


/-- **THE PRESENTATION IS UNIQUE PER LEG SET.**  Two leg lists that pass the sort check, built from the same legs in any
order are the SAME list -- so there is no permuted re-presentation to find.  An attacker cannot reorder
legs to obtain a second `flowId` for one economic flow. -/
abbrev Properties.ascending_unique {l₁ l₂ : List α}
    (hp : l₁.Perm l₂) (h₁ : Ascending l₁) (h₂ : Ascending l₂) :=
  l₁ = l₂


/-! ## Why the check is an ORDERING and not merely distinctness

The natural cheaper guard is "no two ADJACENT legs are equal".  It would pass the same loop shape and
cost the same gas.  It is also unsound, and this is the reason the deployed check uses `<=` rather than
`==`: distinctness is not transitive, so a neighbour scan cannot lift to a global claim. -/

/-- **THE CHEAPER GUARD FAILS.**  Adjacent-distinct admits a duplicated leg at distance two, which
would put the same bundle hash in one flow twice -- the case `no_duplicate_leg` rules out only because
the deployed relation is transitive. -/
abbrev Properties.neighbour_distinct_insufficient :=
  ∃ l : List ℕ, l.IsChain (· ≠ ·) ∧ ¬ l.Nodup


/-- And it admits a permuted re-presentation too: same legs, different list, both passing. -/
abbrev Properties.neighbour_distinct_admits_permutation :=
  ∃ l₁ l₂ : List ℕ, l₁.IsChain (· ≠ ·) ∧ l₂.IsChain (· ≠ ·) ∧ l₁.Perm l₂ ∧ l₁ ≠ l₂


/-- **EVERY LEG HAS EXACTLY ONE SOURCE CHAIN.**  The zipped pairing has distinct keys and loses no
leg, so a flow passing the sort and length checks (so every flow `_validateAndComputeFlowId` accepts) really is a
function from bundle hash to source chain: the same leg cannot be
presented as originating on two different chains within one flow. -/
abbrev Properties.valid_pairing_functional {β : Type*} {f : Flow α β} (h : Valid f) :=
  ((f.legs.zip f.chains).map Prod.fst).Nodup ∧ (f.legs.zip f.chains).length = f.legs.length


/-- **NO INJECTED DUPLICATE.**  Restated on the flow: distinct leg positions are distinct legs. -/
abbrev Properties.valid_no_duplicate_leg {β : Type*} {f : Flow α β} (h : Valid f)
    {i j : Fin f.legs.length} (hne : i ≠ j) :=
  f.legs.get i ≠ f.legs.get j


/-- **NO PERMUTED RE-PRESENTATION.**  Two flows passing the sort and length checks over the same legs
have identical leg lists.  So two preimages of one economic flow that differ only by the order of their
legs cannot both be accepted.  This says nothing about the hash: no `abi.encode` injectivity for the
`b17415d20` preimage struct is proved here (`Specs/FlowCanonicalAtV35.lean`). -/
abbrev Properties.valid_unique_per_leg_set {β : Type*} {f g : Flow α β}
    (hf : Valid f) (hg : Valid g) (hp : f.legs.Perm g.legs) :=
  f.legs = g.legs


end AttackVectors.FlowCanonical
