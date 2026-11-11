import EraSpec.Contracts.AtomicFlowManager.Properties.FlowCanonical
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


/-- **NEIGHBOURS GIVE ALL PAIRS.**  The bridge from the loop to the global claims: because `<` is
transitive, scanning adjacent pairs pins every pair of positions. -/
theorem ascending_iff_pairwise {l : List α} :
    Properties.ascending_iff_pairwise (l := l) := by
  unfold Properties.ascending_iff_pairwise
  exact
    List.isChain_iff_pairwise


/-- Strictly ascending at every earlier/later position pair. -/
theorem ascending_lt_of_lt {l : List α} (h : Ascending l) {i j : Fin l.length} (hij : i < j) :
    Properties.ascending_lt_of_lt (l := l) (h := h) (i := i) (j := j) (hij := hij) := by
  unfold Properties.ascending_lt_of_lt
  exact
    (List.pairwise_iff_get.mp (ascending_iff_pairwise.mp h)) i j hij


/-- **NO DUPLICATED LEG.**  Distinct positions carry distinct bundle hashes -- so a flow cannot list
the same leg twice, at any distance.  The loop never compares position 0 with position 5; this is why
it does not have to. -/
theorem no_duplicate_leg {l : List α} (h : Ascending l) {i j : Fin l.length} (hne : i ≠ j) :
    Properties.no_duplicate_leg (l := l) (h := h) (i := i) (j := j) (hne := hne) := by
  unfold Properties.no_duplicate_leg
  exact
    by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact ne_of_lt (ascending_lt_of_lt h hlt)
      · exact (ne_of_lt (ascending_lt_of_lt h hgt)).symm


theorem ascending_nodup {l : List α} (h : Ascending l) :
    Properties.ascending_nodup (l := l) (h := h) := by
  unfold Properties.ascending_nodup
  exact
    (ascending_iff_pairwise.mp h).imp ne_of_lt


/-- **THE PRESENTATION IS UNIQUE PER LEG SET.**  Two accepted flows built from the same legs in any
order are the SAME list -- so there is no permuted re-presentation to find.  An attacker cannot reorder
legs to obtain a second `flowId` for one economic flow. -/
theorem ascending_unique {l₁ l₂ : List α}
    (hp : l₁.Perm l₂) (h₁ : Ascending l₁) (h₂ : Ascending l₂) :
    Properties.ascending_unique (l₁ := l₁) (l₂ := l₂) (hp := hp) (h₁ := h₁) (h₂ := h₂) := by
  unfold Properties.ascending_unique
  exact
    by
      exact hp.eq_of_pairwise (fun _ _ _ _ hab hba => absurd hab (asymm hba))
        (ascending_iff_pairwise.mp h₁) (ascending_iff_pairwise.mp h₂)


/-! ## Why the check is an ORDERING and not merely distinctness

The natural cheaper guard is "no two ADJACENT legs are equal".  It would pass the same loop shape and
cost the same gas.  It is also unsound, and this is the reason the deployed check uses `<=` rather than
`==`: distinctness is not transitive, so a neighbour scan cannot lift to a global claim. -/

/-- **THE CHEAPER GUARD FAILS.**  Adjacent-distinct admits a duplicated leg at distance two, which
would put the same bundle hash in one flow twice -- the case `no_duplicate_leg` rules out only because
the deployed relation is transitive. -/
theorem neighbour_distinct_insufficient :
    Properties.neighbour_distinct_insufficient := by
  unfold Properties.neighbour_distinct_insufficient
  exact
    by
      refine ⟨[1, 2, 1], by simp [List.isChain_cons], by decide⟩


/-- And it admits a permuted re-presentation too: same legs, different list, both passing. -/
theorem neighbour_distinct_admits_permutation :
    Properties.neighbour_distinct_admits_permutation := by
  unfold Properties.neighbour_distinct_admits_permutation
  exact
    by
      refine ⟨[1, 2], [2, 1], by simp [List.isChain_cons], by simp [List.isChain_cons], ?_, by decide⟩
      exact List.Perm.swap _ _ _


/-- **EVERY LEG HAS EXACTLY ONE SOURCE CHAIN.**  The zipped pairing has distinct keys and loses no
leg, so an accepted flow really is a function from bundle hash to source chain: the same leg cannot be
presented as originating on two different chains within one flow. -/
theorem valid_pairing_functional {β : Type*} {f : Flow α β} (h : Valid f) :
    Properties.valid_pairing_functional (β := β) (f := f) (h := h) := by
  unfold Properties.valid_pairing_functional
  exact
    by
      have hlen : min f.legs.length f.chains.length = f.legs.length := by
        rw [h.2]; exact min_self _
      constructor
      · have : (f.legs.zip f.chains).map Prod.fst = f.legs := by
          rw [List.map_fst_zip]
          exact le_of_eq h.2.symm
        rw [this]; exact ascending_nodup h.1
      · rw [List.length_zip]; exact hlen


/-- **NO INJECTED DUPLICATE.**  Restated on the flow: distinct leg positions are distinct legs. -/
theorem valid_no_duplicate_leg {β : Type*} {f : Flow α β} (h : Valid f)
    {i j : Fin f.legs.length} (hne : i ≠ j) :
    Properties.valid_no_duplicate_leg (β := β) (f := f) (h := h) (i := i) (j := j) (hne := hne) := by
  unfold Properties.valid_no_duplicate_leg
  exact
    no_duplicate_leg h.1 hne


/-- **NO PERMUTED RE-PRESENTATION.**  Two accepted flows over the same legs have identical leg lists,
hence identical `abi.encode` preimages for that field -- so a second `flowId` for one flow would need a
keccak collision, not a reordering.  Pairs with `BundleHashEncoding.abiEncode_inj`, which rules out the
encoding-level route for the other field. -/
theorem valid_unique_per_leg_set {β : Type*} {f g : Flow α β}
    (hf : Valid f) (hg : Valid g) (hp : f.legs.Perm g.legs) :
    Properties.valid_unique_per_leg_set (β := β) (f := f) (g := g) (hf := hf) (hg := hg) (hp := hp) := by
  unfold Properties.valid_unique_per_leg_set
  exact
    ascending_unique hp hf.1 hg.1


end AttackVectors.FlowCanonical
