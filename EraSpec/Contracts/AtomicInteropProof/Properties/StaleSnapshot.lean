import EraSpec.Contracts.AtomicInteropProof.Specs.StaleSnapshot

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false


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


/-- **(a) A WITNESS IS ONLY EVER STALE.**  Along any evolution from a sound
base, a reclaim witness for `v` at snapshot `j` together with delivery of
`v` at snapshot `n` forces `j < n`: the witness predates the delivery.  At
or after delivery (`n ≤ j`), membership persists (`evolution_keys_mono`)
and kills every straddling window (`present_not_reclaimable`), so no
witness can exist there.  A snapshot-`j` witness proves absence at `j` —
and nothing about any later snapshot. -/
abbrev Properties.witness_precedes_delivery {S : ℕ → Finset AbsLeaf} {v : UInt256}
    (hevo : Evolution S) (h0 : SoundState (S 0))
    {j n : ℕ} {W : AbsLeaf}
    (hW : W ∈ S j) (hlow : W.key < v) (hwin : W.nextKey = 0 ∨ v < W.nextKey)
    (hdel : v ∈ keys (S n)) :=
  j < n


/-- **(b) A STALE WITNESS CANNOT BE REDEEMED AFTER AN ON-TIME DELIVERY.**
The reclaim gate accepts a witness only at a DEADLINE-PINNED snapshot `j`
(`D < t (j+1)`: `j` is the last snapshot settled by the deadline); the
delivery gate accepts membership only at an ON-TIME snapshot (`t i ≤ D`).
Under these gates a witness accepted at `j` entails that `v` is a key of
NO on-time snapshot — the attacker's early witness and any on-time
delivery are mutually exclusive.  Packaging of
`delivered_and_reclaimed_impossible`. -/
abbrev Properties.stale_witness_not_redeemable {S : ℕ → Finset AbsLeaf} {t : ℕ → UInt256} {D v : UInt256}
    (hevo : Evolution S) (h0 : SoundState (S 0)) (htmono : Monotone t)
    {j : ℕ} {W : AbsLeaf}
    (hpin : D < t (j+1))
    (hW : W ∈ S j) (hlow : W.key < v) (hwin : W.nextKey = 0 ∨ v < W.nextKey) :=
  ∀ i : ℕ, t i ≤ D → v ∉ keys (S i)


/-- **(b, attacker's view) THE PINNING CHECK IS EXACTLY WHAT FAILS.**  Given
an actual on-time delivery of `v` (`t i ≤ D`, `v ∈ keys (S i)`), NO
snapshot carrying a reclaim witness for `v` can pass the pinning check
`D < t (j+1)`.  The attacker's stale witness is genuine — absence at `j`
really held — but the reclaim gate's timestamp comparison is precisely the
condition it can never satisfy.  Contrapositive packaging of
`delivered_and_reclaimed_impossible`. -/
abbrev Properties.pinning_gate_rejects_stale_witness {S : ℕ → Finset AbsLeaf} {t : ℕ → UInt256} {D v : UInt256}
    (hevo : Evolution S) (h0 : SoundState (S 0)) (htmono : Monotone t)
    {i : ℕ} (hti : t i ≤ D) (hdel : v ∈ keys (S i))
    {j : ℕ} {W : AbsLeaf}
    (hW : W ∈ S j) (hlow : W.key < v) (hwin : W.nextKey = 0 ∨ v < W.nextKey) :=
  ¬ D < t (j+1)


/-- **(c) SHARPNESS: WITHOUT THE DEADLINE GATE, THE ATTACK STATE EXISTS.**
For any nonzero commit value `a` there is an `Evolution` from the sound
genesis, snapshots `j < n`, and a leaf `W` such that `W` is a GENUINE
reclaim witness for `a` at snapshot `j` while `a` IS delivered at snapshot
`n`.  (Concretely: `S 0 = {⟨0,0⟩}`, `S n = imtInsert {⟨0,0⟩} ⟨0,0⟩ a` for
`n ≥ 1`; the genesis leaf `⟨0,0⟩` witnesses absence at `j = 0`, and `a` is
a key of `S 1`.)

What this shows: witness-existence at one snapshot and delivery at another
coexist in sound histories, so any reclaim gate that accepts a witness
without comparing its snapshot's settlement time to the deadline pays a
refund on a delivered leg.  What it does NOT show: a violation of the
GATED protocol — here `j < n` (as `witness_precedes_delivery` forces), and
no monotone timestamps can satisfy both gates for this pair (that is
`stale_witness_not_redeemable`).  The timestamp comparison, and it alone,
is what separates this sound-but-dangerous state from an actual theft. -/
abbrev Properties.deadline_gate_indispensable {a : UInt256} (ha : a ≠ 0) :=
  ∃ (S : ℕ → Finset AbsLeaf) (j n : ℕ) (W : AbsLeaf),
        Evolution S ∧ SoundState (S 0)
          ∧ j < n
          ∧ W ∈ S j ∧ W.key < a ∧ (W.nextKey = 0 ∨ a < W.nextKey)
          ∧ a ∈ keys (S n)


end AttackVectors.StaleSnapshot
