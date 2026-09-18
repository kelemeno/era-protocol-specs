import EraSpec.Core.IMT

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
theorem witness_precedes_delivery
    {S : ℕ → Finset AbsLeaf} {v : UInt256}
    (hevo : Evolution S) (h0 : SoundState (S 0))
    {j n : ℕ} {W : AbsLeaf}
    (hW : W ∈ S j) (hlow : W.key < v) (hwin : W.nextKey = 0 ∨ v < W.nextKey)
    (hdel : v ∈ keys (S n)) :
    j < n := by
  by_contra h
  push_neg at h
  have hkeys : v ∈ keys (S j) := evolution_keys_mono hevo h hdel
  exact present_not_reclaimable (evolution_sound hevo h0 j).1 hkeys
    ⟨W, hW, hlow, hwin⟩

/-- **(b) A STALE WITNESS CANNOT BE REDEEMED AFTER AN ON-TIME DELIVERY.**
The reclaim gate accepts a witness only at a DEADLINE-PINNED snapshot `j`
(`D < t (j+1)`: `j` is the last snapshot settled by the deadline); the
delivery gate accepts membership only at an ON-TIME snapshot (`t i ≤ D`).
Under these gates a witness accepted at `j` entails that `v` is a key of
NO on-time snapshot — the attacker's early witness and any on-time
delivery are mutually exclusive.  Packaging of
`delivered_and_reclaimed_impossible`. -/
theorem stale_witness_not_redeemable
    {S : ℕ → Finset AbsLeaf} {t : ℕ → UInt256} {D v : UInt256}
    (hevo : Evolution S) (h0 : SoundState (S 0)) (htmono : Monotone t)
    {j : ℕ} {W : AbsLeaf}
    (hpin : D < t (j+1))
    (hW : W ∈ S j) (hlow : W.key < v) (hwin : W.nextKey = 0 ∨ v < W.nextKey) :
    ∀ i : ℕ, t i ≤ D → v ∉ keys (S i) := by
  intro i hti hmem
  exact delivered_and_reclaimed_impossible hevo h0.1 h0.2.1 htmono
    hti hmem hpin hW hlow hwin

/-- **(b, attacker's view) THE PINNING CHECK IS EXACTLY WHAT FAILS.**  Given
an actual on-time delivery of `v` (`t i ≤ D`, `v ∈ keys (S i)`), NO
snapshot carrying a reclaim witness for `v` can pass the pinning check
`D < t (j+1)`.  The attacker's stale witness is genuine — absence at `j`
really held — but the reclaim gate's timestamp comparison is precisely the
condition it can never satisfy.  Contrapositive packaging of
`delivered_and_reclaimed_impossible`. -/
theorem pinning_gate_rejects_stale_witness
    {S : ℕ → Finset AbsLeaf} {t : ℕ → UInt256} {D v : UInt256}
    (hevo : Evolution S) (h0 : SoundState (S 0)) (htmono : Monotone t)
    {i : ℕ} (hti : t i ≤ D) (hdel : v ∈ keys (S i))
    {j : ℕ} {W : AbsLeaf}
    (hW : W ∈ S j) (hlow : W.key < v) (hwin : W.nextKey = 0 ∨ v < W.nextKey) :
    ¬ D < t (j+1) :=
  fun hpin => delivered_and_reclaimed_impossible hevo h0.1 h0.2.1 htmono
    hti hdel hpin hW hlow hwin

/-! ## Sharpness — the deadline gate is indispensable

The two theorems above lean entirely on the timestamp gates.  The history
below shows they must: in a perfectly sound `Evolution`, a genuine reclaim
witness at one snapshot and delivery at a later snapshot COEXIST.  A gate
that merely demanded "a valid witness at SOME snapshot" — without comparing
that snapshot's settlement time against the deadline — would accept the
stale witness and pay the refund on a delivered leg. -/

/-- The minimal stale-witness history: genesis at step 0, one guarded insert
of `a` at the 0 → 1 boundary, constant thereafter. -/
private def staleHistory (a : UInt256) : ℕ → Finset AbsLeaf :=
  fun m => if m = 0 then {⟨0, 0⟩} else imtInsert {⟨0, 0⟩} ⟨0, 0⟩ a

/-- The stale-witness history is a genuine `Evolution`: step 0 is the
guarded insert of `a` through the genesis leaf's window, every later step
is a no-op. -/
private theorem staleHistory_evolution {a : UInt256} (ha : a ≠ 0) :
    Evolution (staleHistory a) := by
  intro n
  cases n with
  | zero =>
    exact Or.inr ⟨⟨0, 0⟩, a, Finset.mem_singleton_self _,
      Fin.pos_of_ne_zero ha, Or.inl rfl, rfl⟩
  | succ k =>
    exact Or.inl rfl

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
theorem deadline_gate_indispensable {a : UInt256} (ha : a ≠ 0) :
    ∃ (S : ℕ → Finset AbsLeaf) (j n : ℕ) (W : AbsLeaf),
      Evolution S ∧ SoundState (S 0)
        ∧ j < n
        ∧ W ∈ S j ∧ W.key < a ∧ (W.nextKey = 0 ∨ a < W.nextKey)
        ∧ a ∈ keys (S n) := by
  refine ⟨staleHistory a, 0, 1, ⟨0, 0⟩,
    staleHistory_evolution ha, genesis_soundState, Nat.zero_lt_one,
    Finset.mem_singleton_self _, Fin.pos_of_ne_zero ha, Or.inl rfl, ?_⟩
  exact imtInsert_key_mem (Finset.mem_singleton_self _)

end AttackVectors.StaleSnapshot
