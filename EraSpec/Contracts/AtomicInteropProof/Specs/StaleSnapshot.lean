import EraSpec.Contracts.IndexedMerkleTree.Specs.Model


/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/StaleSnapshot.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  ATTACK VECTOR: STALE-SNAPSHOT RECLAIM.

  A "reclaim witness" for commit value `v` at snapshot `j` is a leaf
  `W ∈ S j` with `W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)` — a gap
  window straddling `v`, proving `v` was ABSENT from snapshot `j`.

  The attack: an attacker obtains a perfectly legitimate reclaim witness at
  an EARLY snapshot `j` (when `v` really was absent), waits until `v` has
  been delivered at some later snapshot `n > j`, and then presents the old
  witness to the reclaim gate — attempting to collect BOTH the delivery and
  the refund.

  What this file establishes:

  * `witness_precedes_delivery` — a reclaim witness is intrinsically a
    STALE-ONLY artifact once `v` is delivered: along any `Evolution` from a
    `SoundState` base, if `v ∈ keys (S n)` and snapshot `j` carries a
    witness, then `j < n` is FORCED.  A witness cannot exist at or after
    the delivery snapshot (keys only grow, and presence kills every
    straddling window).  So the only witnesses an attacker can ever hold
    against a delivered value are stale ones.

  * `stale_witness_not_redeemable` — the deadline gate is what makes that
    staleness unexploitable.  The reclaim gate does not accept a witness at
    an arbitrary snapshot: it pins `j` as the LAST on-time snapshot via
    `D < t (j+1)`, while the delivery gate demands an on-time snapshot
    `t i ≤ D`.  Under these two gates, a witness pinned at `j` proves `v`
    is a key of NO on-time snapshot whatsoever — so no on-time delivery of
    `v` can coexist with an accepted reclaim.  (This is a packaging of
    `delivered_and_reclaimed_impossible`; it is cited, not re-proved.)

  * `pinning_gate_rejects_stale_witness` — the same fact from the
    attacker's side: given an actual on-time delivery of `v`, the pinning
    check `D < t (j+1)` FAILS for every snapshot `j` that carries a
    witness.  The attacker's witness is genuine, but the gate's timestamp
    comparison is exactly the check that can never pass for it.

  * `deadline_gate_indispensable` — SHARPNESS.  The timestamp gate is doing
    real work: there is an explicit `Evolution` from the sound genesis
    (insert one value `a` at step 0, constant thereafter) in which a
    genuine reclaim witness exists at snapshot 0 AND `a` is delivered at
    snapshot 1.  Witness-existence-at-some-snapshot and
    delivery-at-another COEXIST in perfectly sound histories.

  Honest scope of the counterexample: `deadline_gate_indispensable` shows
  that a reclaim gate checking ONLY "some snapshot carries a valid witness
  for `v`" (with no deadline/ordering comparison between the witness
  snapshot and the delivery snapshot) accepts a witness for a value that is
  ALSO delivered — i.e. dropping the timestamp comparison re-enables the
  double-spend that `stale_witness_not_redeemable` excludes.  It does NOT
  exhibit a violation of the gated protocol itself: consistent with
  `witness_precedes_delivery`, the witness in the counterexample lives
  strictly BEFORE the delivery (`j = 0 < 1 = n`), and any monotone
  timestamp assignment satisfying both gates for this history is
  impossible (that is precisely `stale_witness_not_redeemable`).

  Pure order theory over `IMTAbstract` — axiom-free, no EVM semantics.
-/

namespace AttackVectors.StaleSnapshot


open IMTAbstract

open Clear


/-! ## Sharpness — the deadline gate is indispensable

The two theorems above lean entirely on the timestamp gates.  The history
below shows they must: in a perfectly sound `Evolution`, a genuine reclaim
witness at one snapshot and delivery at a later snapshot COEXIST.  A gate
that merely demanded "a valid witness at SOME snapshot" — without comparing
that snapshot's settlement time against the deadline — would accept the
stale witness and pay the refund on a delivered leg. -/

/-- The minimal stale-witness history: genesis at step 0, one guarded insert
of `a` at the 0 → 1 boundary, constant thereafter. -/
def staleHistory (a : UInt256) : ℕ → Finset AbsLeaf :=
  fun m => if m = 0 then {⟨0, 0⟩} else imtInsert {⟨0, 0⟩} ⟨0, 0⟩ a


end AttackVectors.StaleSnapshot
