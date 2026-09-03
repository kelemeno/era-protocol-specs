import EraSpec.Core.IMT

/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/NoTheft.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  NO THEFT — the master abstract-layer capstone for one bridge leg.

  A bridge leg is identified by its commit value `v` (nonzero — `0` is the
  genesis sentinel key).  An attacker PROFITS on a leg iff they obtain value
  they are not entitled to, i.e. iff at least one of the following happens:

  * DOUBLE REDEMPTION — the leg is both delivered (its value `v` is a key of
    a snapshot settled on time, `t i ≤ D`) and refunded (a valid reclaim
    witness for `v` is accepted at the deadline-pinned snapshot `j`,
    `D < t (j+1)`);
  * FALSE REFUND — a refund is obtained for a leg that WAS delivered;
  * DOUBLE DELIVERY — the same leg is delivered twice (enters the tree at two
    distinct steps).

  This file proves each of these impossible for any `GuardedEvolution` from
  the genesis singleton `{⟨0,0⟩}` — the exact history shape a real contract
  run has — and bundles them into the single headline theorem `no_theft`:
  each leg has EXACTLY ONE outcome (delivered XOR reclaimable), that outcome
  is PERMANENT, and delivery happens at EXACTLY ONE step.

  ────────────────────────────────────────────────────────────────────────────
  ASSUMPTION LEDGER
  ────────────────────────────────────────────────────────────────────────────

  ## ESTABLISHED (what the theorems actually prove)

  For every history `S : ℕ → Finset AbsLeaf` satisfying `GuardedEvolution S`
  (each step is a no-op or an insert guarded by: low leaf `W ∈ S n`,
  `W.key < v`, weak window `W.nextKey = 0 ∨ v ≤ W.nextKey`, dedup
  `v ∉ keys (S n)`), started at `S 0 = {⟨0,0⟩}`, with monotone settlement
  timestamps `t` and any deadline `D`, and every nonzero commit value `v`:

  * `no_double_redemption` — on-time delivery evidence (`t i ≤ D`,
    `v ∈ keys (S i)`) and a deadline-pinned reclaim witness (`D < t (j+1)`,
    a leaf of `S j` whose window straddles `v`) can NEVER coexist.
  * `exactly_one_outcome` — at any (in particular any deadline-pinned)
    snapshot, EXACTLY ONE of {`v` delivered, `v` reclaimable} holds: never
    both (no false refund of a delivered leg) and never neither (a
    non-delivered leg is always refundable).
  * `no_second_delivery` — there are no two distinct steps at which `v`
    transitions from absent to present: delivery is at most once (and
    `guardedEvolution_delivery_exactly_once` makes it exactly once for any
    delivered value).
  * `delivery_is_final` — once delivered on time, `v` is a key of EVERY
    later snapshot and NO deadline-pinned snapshot ever carries a reclaim
    witness for it: the delivered outcome is permanent and unrevokable.
  * `no_theft` — the conjunction of all of the above in one statement.

  All proofs REUSE the analytic corpus of `IMTAbstract`
  (`delivered_and_reclaimed_impossible`, `reclaimable_iff_absent`,
  `evolution_key_origin`/`_unique`, `evolution_keys_mono`) through the
  refinement `guardedEvolution_isEvolution`; nothing is re-proved here.
  No `sorry`, no new axioms; pure order theory over finite leaf sets.

  ## HYPOTHESES DISCHARGED BY THE CALLER

  Every hypothesis of `no_theft`, why the real system must supply it, and
  the sharpness counterexample showing it is load-bearing:

  1. `hge : GuardedEvolution S` — every state change of the leaf set is a
     no-op or THE guarded insert: low leaf a member, `W.key < v`, weak
     window, dedup gate.  This is the concrete-layer obligation on the
     `L2InteropCommitmentTree` insert path (the ONLY public mutator).  Drop
     any conjunct and theft returns:
       * membership of the presented low leaf —
         `IMTAbstract.forged_padding_witness_breaks_exclusivity` exhibits a
         sound tree where a NON-member leaf straddles a delivered value
         (the padding-hash forgery);
       * the window/ordering guards —
         `AttackVectors.InsertGuard.below_window_insert_breaks_windowPos`
         shows an unguarded insert destroys the list invariants;
       * the dedup gate —
         `AttackVectors.InsertGuard.weak_window_without_dedup_breaks_keyInj`
         shows the weak loop-exit window alone admits a duplicate key
         (`AttackVectors.InsertGuard.duplicate_delivery_blocked` shows the
         gate is exactly what blocks it).
  2. `hgen : S 0 = {⟨0,0⟩}` — the tree is initialized ONCE to the genesis
     singleton and never re-initialized: the history index `n` spans the
     tree's ENTIRE lifetime.  A mid-life reset is not a mis-guarded step but
     a violation of the history shape itself —
     `AttackVectors.ResetAndZero.resetHistory_not_evolution` proves a
     deliver-then-reset history satisfies NO `Evolution`, and
     `resetHistory_forgets` shows it re-opens reclaim for a delivered value.
     The contract must enforce one-time initialization.
  3. `htmono : Monotone t` — settlement timestamps are non-decreasing in
     settlement order.  This is a property of the SETTLEMENT LAYER (L1
     block timestamps / batch ordering), not of the tree.
     `AttackVectors.Timestamps.monotone_timestamps_indispensable` exhibits,
     for non-monotone `t`, a guarded-from-genesis history carrying BOTH
     on-time delivery evidence and a deadline-pinned reclaim witness for the
     same value — double redemption.  Without it, clauses (1)-only-one and
     (2) of `no_theft` are FALSE.
  4. `hv0 : v ≠ 0` — the commit value is nonzero.  `0` is the genesis
     sentinel key: it is "delivered" at birth without any insert
     (`AttackVectors.ResetAndZero.zero_always_present`) and never
     reclaimable (`zero_never_reclaimable`), so no leg may be given commit
     value `0`.  The concrete commit value is a keccak hash of the bundle;
     the caller must ensure the zero case is rejected (the guarded insert
     itself can never insert 0 — `guarded_never_inserts_zero`).

  Additionally, the DELIVERY-side hypotheses `t i ≤ D` / pin `D < t (j+1)`
  are the gate comparisons the contract performs at redemption time; the
  reclaim-pinning gate is load-bearing too —
  `AttackVectors.StaleSnapshot.deadline_gate_indispensable` shows accepting
  a gap witness at an UNPINNED (stale) snapshot re-admits double redemption.

  ## OUT OF SCOPE / NOT PROVED HERE

  (i)  This is the ABSTRACT set-level layer.  It does NOT by itself prove
       that the deployed EVM bytecode implements `GuardedEvolution` — that
       every storage-mutating path of the real `L2InteropCommitmentTree` /
       `AtomicFlowManager` is a no-op or the guarded insert on the
       represented leaf set.  That is the concrete-layer obligation
       (discharged per-function against the Yul VCs; the bridge lemmas
       `image_insert_step'` / `guarded_insert_sound_step` in `IMTAbstract`
       are its designated landing points).
  (ii) Merkle-ROOT binding of the leaf set is separate: the gates verify
       proofs against a 32-byte root, not against the set itself.  That
       roots pin leaf sets is `MerkleSpec` (M-D) plus
       `AttackVectors.RootForgery`, and it depends on node-hash
       PAIR-INJECTIVITY as a HYPOTHESIS standing in for keccak collision
       resistance — a cryptographic assumption, not a theorem.
  (iii) The capacity bound (no more inserts than the tree's arity^depth) and
       padding DOMAIN SEPARATION (empty-slot padding distinguishable from
       `hashLeaf {0,0,0}`) are additional concrete obligations —
       `AttackVectors.TreeShape.capacity_overflow_forges_root` and
       `padding_ambiguity_forges_root` show each failing is exploitable, and
       `IMTAbstract.forged_padding_witness_breaks_exclusivity` shows the
       padding forgery defeats the reclaim gate directly.
  (iv) GOVERNANCE IS EXCEPTED — an authorised reset / upgrade / storage
       surgery is outside the `Evolution` model BY CONSTRUCTION
       (`AttackVectors.ResetAndZero.resetHistory_not_evolution`): nothing
       here constrains a privileged actor who can rewrite state or code.
       "No theft" is proven against unprivileged users of the public
       interface only.

  Nothing in this file claims end-to-end safety of the deployed system; it
  claims exactly: IF the concrete layer supplies hypotheses 1–4 (and the
  separate obligations (i)–(iii)), THEN no leg can be redeemed twice, no
  delivered leg refunded, and no leg delivered twice.
-/

namespace AttackVectors.NoTheft

open IMTAbstract
open Clear

/-! ## Vocabulary — the three per-leg predicates the gates decide -/

/-- Commit value `v` is DELIVERED at snapshot `j`: it is a key of the leaf
set — what the delivery gate's membership proof establishes. -/
def Delivered (S : ℕ → Finset AbsLeaf) (v : UInt256) (j : ℕ) : Prop :=
  v ∈ keys (S j)

/-- Commit value `v` is RECLAIMABLE at snapshot `j`: some tree leaf's window
straddles `v` — exactly the witness the reclaim gate demands. -/
def Reclaimable (S : ℕ → Finset AbsLeaf) (v : UInt256) (j : ℕ) : Prop :=
  ∃ W ∈ S j, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)

/-- Commit value `v` ENTERS the tree at step `m`: absent at `m`, present at
`m+1`.  Delivery events are exactly the entry steps. -/
def EntersAt (S : ℕ → Finset AbsLeaf) (v : UInt256) (m : ℕ) : Prop :=
  v ∉ keys (S m) ∧ v ∈ keys (S (m + 1))

/-- A nonzero value is not a key of the genesis singleton. -/
private lemma genesis_absent
    {S : ℕ → Finset AbsLeaf} (hgen : S 0 = ({⟨0, 0⟩} : Finset AbsLeaf))
    {v : UInt256} (hv0 : v ≠ 0) : v ∉ keys (S 0) := by
  rw [hgen]
  intro hmem
  obtain ⟨L, hL, hLkey⟩ := Finset.mem_image.mp hmem
  rw [Finset.mem_singleton] at hL
  rw [hL] at hLkey
  exact hv0 hLkey.symm

/-- The genesis singleton discharges `SoundState (S 0)`. -/
private lemma genesis_sound
    {S : ℕ → Finset AbsLeaf} (hgen : S 0 = ({⟨0, 0⟩} : Finset AbsLeaf)) :
    SoundState (S 0) := by
  rw [hgen]; exact genesis_soundState

/-! ## The four attack impossibilities -/

/-- **NO DOUBLE REDEMPTION.**  Along any guarded history from genesis with
monotone settlement timestamps, it is impossible for one commit value `v` to
carry BOTH on-time delivery evidence (`t i ≤ D`, `v` a key of `S i`) AND a
deadline-pinned reclaim witness (`D < t (j+1)`, a leaf of `S j` whose window
straddles `v`).  An attacker can never collect the leg and its refund.
Packaging of `IMTAbstract.delivered_and_reclaimed_impossible` through
`guardedEvolution_isEvolution` (cited, not re-proved). -/
theorem no_double_redemption
    {S : ℕ → Finset AbsLeaf} {t : ℕ → UInt256} {D v : UInt256}
    (hge : GuardedEvolution S) (hgen : S 0 = ({⟨0, 0⟩} : Finset AbsLeaf))
    (htmono : Monotone t)
    {i : ℕ} (hti : t i ≤ D) (hdel : Delivered S v i)
    {j : ℕ} (htj1 : D < t (j + 1)) (hrec : Reclaimable S v j) :
    False := by
  obtain ⟨W, hW, hlow, hwin⟩ := hrec
  have h0 := genesis_sound hgen
  exact delivered_and_reclaimed_impossible (guardedEvolution_isEvolution hge h0)
    h0.1 h0.2.1 htmono hti hdel htj1 hW hlow hwin

/-- **EXACTLY ONE OUTCOME.**  At a deadline-pinned snapshot `j` (`D < t (j+1)`
— the snapshot the reclaim gate reads), a nonzero commit value is EITHER
delivered OR reclaimable, and NEVER both: no leg is stuck (never neither) and
no delivered leg is refundable (never both).  Direct consequence of
`guardedEvolution_reclaimable_iff_absent`.  The dichotomy in fact holds at
EVERY snapshot — the pin hypothesis records the reclaim gate's precondition
and is not needed for the set-level fact, which is why it is unnamed. -/
theorem exactly_one_outcome
    {S : ℕ → Finset AbsLeaf} {t : ℕ → UInt256} {D v : UInt256}
    (hge : GuardedEvolution S) (hgen : S 0 = ({⟨0, 0⟩} : Finset AbsLeaf))
    (hv0 : v ≠ 0) {j : ℕ} (_hpin : D < t (j + 1)) :
    (Delivered S v j ∨ Reclaimable S v j)
      ∧ ¬ (Delivered S v j ∧ Reclaimable S v j) := by
  have hiff := guardedEvolution_reclaimable_iff_absent hge hgen (j := j) hv0
  constructor
  · by_cases h : v ∈ keys (S j)
    · exact Or.inl h
    · exact Or.inr (hiff.mpr h)
  · rintro ⟨hdel, hrec⟩
    exact hiff.mp hrec hdel

/-- **NO SECOND DELIVERY.**  Along any guarded history from genesis there are
no two DISTINCT steps at which the same commit value transitions from absent
to present: a leg enters the tree at most once.  (Existence of the entry step
for any delivered value — hence EXACTLY once — is
`guardedEvolution_delivery_exactly_once`; this is its uniqueness half restated
as an attack impossibility, via `evolution_key_origin_unique`.) -/
theorem no_second_delivery
    {S : ℕ → Finset AbsLeaf}
    (hge : GuardedEvolution S) (hgen : S 0 = ({⟨0, 0⟩} : Finset AbsLeaf))
    {v : UInt256} :
    ¬ ∃ m₁ m₂ : ℕ, m₁ ≠ m₂ ∧ EntersAt S v m₁ ∧ EntersAt S v m₂ := by
  rintro ⟨m₁, m₂, hne, h1, h2⟩
  exact hne (evolution_key_origin_unique
    (guardedEvolution_isEvolution hge (genesis_sound hgen)) h1 h2)

/-- **DELIVERY IS FINAL.**  On-time delivery evidence for `v` persists at
EVERY later snapshot (any chain verifying against any later root accepts the
same leg), and NO deadline-pinned snapshot — ever — carries a reclaim witness
for `v`: the delivered outcome cannot be revoked or converted into a refund.
Packaging of `guardedEvolution_delivered_available_forever`. -/
theorem delivery_is_final
    {S : ℕ → Finset AbsLeaf} {t : ℕ → UInt256} {D v : UInt256}
    (hge : GuardedEvolution S) (hgen : S 0 = ({⟨0, 0⟩} : Finset AbsLeaf))
    (htmono : Monotone t)
    {i : ℕ} (hti : t i ≤ D) (hdel : Delivered S v i) :
    (∀ j, i ≤ j → Delivered S v j)
      ∧ (∀ j, D < t (j + 1) → ¬ Reclaimable S v j) := by
  obtain ⟨hpers, hnorec⟩ :=
    guardedEvolution_delivered_available_forever hge hgen htmono hti hdel
  refine ⟨hpers, ?_⟩
  rintro j htj ⟨W, hW, hlow, hwin⟩
  exact hnorec j W htj hW hlow hwin

/-! ## The headline -/

/-- **NO THEFT (master capstone).**  Along any guarded history from the
genesis singleton (`GuardedEvolution S`, `S 0 = {⟨0,0⟩}`) with monotone
settlement timestamps `t`, deadline `D`, and nonzero commit value `v`:

1. **exactly one outcome** — at every deadline-pinned snapshot, `v` is
   delivered or reclaimable, and never both;
2. **no double redemption** — on-time delivery evidence and a deadline-pinned
   reclaim witness never coexist (in particular a refunded leg was never
   delivered on time, and a delivered leg can never be refunded);
3. **the outcome is permanent** — a delivered `v` is a key of every later
   snapshot, unconditionally;
4. **delivery has an entry step** — a delivered `v` entered the tree at some
   definite earlier step; and
5. **the entry step is unique** — `v` never enters twice.

Each leg of a bridge flow therefore has exactly one outcome, that outcome is
permanent, and it is reached at exactly one step: no configuration of
snapshots, witnesses, and timestamps pays the same leg out twice or pays an
undelivered leg's delivery.  (See the file header for the exact hypotheses
the concrete layer must discharge and the sharpness counterexamples showing
each is load-bearing.) -/
theorem no_theft
    {S : ℕ → Finset AbsLeaf} {t : ℕ → UInt256} {D v : UInt256}
    (hge : GuardedEvolution S)
    (hgen : S 0 = ({⟨0, 0⟩} : Finset AbsLeaf))
    (htmono : Monotone t) (hv0 : v ≠ 0) :
    -- 1. exactly one outcome at every deadline-pinned snapshot
    (∀ j : ℕ, D < t (j + 1) →
        (Delivered S v j ∨ Reclaimable S v j)
          ∧ ¬ (Delivered S v j ∧ Reclaimable S v j))
    -- 2. no double redemption, across any pair of snapshots
    ∧ (∀ i j : ℕ, t i ≤ D → Delivered S v i → D < t (j + 1) →
          ¬ Reclaimable S v j)
    -- 3. delivery is permanent
    ∧ (∀ i j : ℕ, Delivered S v i → i ≤ j → Delivered S v j)
    -- 4. a delivered leg has an entry step
    ∧ (∀ n : ℕ, Delivered S v n → ∃ m, m < n ∧ EntersAt S v m)
    -- 5. the entry step is unique
    ∧ (∀ m₁ m₂ : ℕ, EntersAt S v m₁ → EntersAt S v m₂ → m₁ = m₂) := by
  have h0 := genesis_sound hgen
  have hevo := guardedEvolution_isEvolution hge h0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j hpin
    exact exactly_one_outcome hge hgen hv0 hpin
  · intro i j hti hdel hpin hrec
    exact no_double_redemption hge hgen htmono hti hdel hpin hrec
  · intro i j hdel hij
    exact evolution_keys_mono hevo hij hdel
  · intro n hdel
    obtain ⟨m, hmn, habs, hstep⟩ :=
      evolution_key_origin hevo n hdel (genesis_absent hgen hv0)
    exact ⟨m, hmn, habs, by rw [hstep]; exact Finset.mem_insert_self _ _⟩
  · intro m₁ m₂ h1 h2
    exact evolution_key_origin_unique hevo h1 h2

/-! ## The capstone from an arbitrary sound start

`no_theft` requires the history to begin at the genesis singleton `{⟨0,0⟩}`.  That
is the right hypothesis for a freshly deployed tree, but it is stronger than the
proof needs: what the argument actually uses is that the initial state is SOUND,
contains the zero leaf, and does not already contain `v`.

Generalizing matters for deployments that do not start from genesis in the proof's
sense — a tree already in service, or one carried across an upgrade that preserves
the linked-list invariant.  For those, `hgen` is unavailable but the three facts
below are establishable. -/

/-- **NO THEFT FROM ANY SOUND START.**  Same five conclusions as `no_theft`, with
the genesis hypothesis replaced by exactly what the proof consumes: the start state
is sound, contains the zero leaf, and does not already contain `v`.

`no_theft` is the special case where the start is `{⟨0,0⟩}` and the history is a
`GuardedEvolution`, which supplies all of these.

The history hypothesis is `Evolution`, NOT `GuardedEvolution`: the proof only ever
uses the derived `Evolution`, so demanding the guarded form would exclude callers
that establish the strict window directly without a dedup gate — which is exactly
what `ConcreteBridge.ConcreteLeafHistory` provides. -/
theorem no_theft_of_sound_start
    {S : ℕ → Finset AbsLeaf} {t : ℕ → UInt256} {D v : UInt256}
    (hevo : Evolution S)
    (h0 : SoundState (S 0))
    (hzero : (0 : UInt256) ∈ keys (S 0))
    (hvabs : v ∉ keys (S 0))
    (htmono : Monotone t) (hv0 : v ≠ 0) :
    (∀ j : ℕ, D < t (j + 1) →
        (Delivered S v j ∨ Reclaimable S v j)
          ∧ ¬ (Delivered S v j ∧ Reclaimable S v j))
    ∧ (∀ i j : ℕ, t i ≤ D → Delivered S v i → D < t (j + 1) → ¬ Reclaimable S v j)
    ∧ (∀ i j : ℕ, Delivered S v i → i ≤ j → Delivered S v j)
    ∧ (∀ n : ℕ, Delivered S v n → ∃ m, m < n ∧ EntersAt S v m)
    ∧ (∀ m₁ m₂ : ℕ, EntersAt S v m₁ → EntersAt S v m₂ → m₁ = m₂) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j _
    constructor
    · by_cases hd : v ∈ keys (S j)
      · exact Or.inl hd
      · exact Or.inr (reclaim_witness_available hevo h0 hzero hv0 hd)
    · rintro ⟨hd, hr⟩
      exact present_not_reclaimable (evolution_sound hevo h0 j).1 hd hr
  · intro i j hti hdel hpin hrec
    obtain ⟨W, hW, hlow, hwin⟩ := hrec
    exact delivered_and_reclaimed_impossible hevo h0.1 h0.2.1 htmono hti hdel hpin hW hlow hwin
  · intro i j hdel hij
    exact evolution_keys_mono hevo hij hdel
  · intro n hdel
    obtain ⟨m, hmn, habs, hstep⟩ := evolution_key_origin hevo n hdel hvabs
    exact ⟨m, hmn, habs, by rw [hstep]; exact Finset.mem_insert_self _ _⟩
  · intro m₁ m₂ h1 h2
    exact evolution_key_origin_unique hevo h1 h2

end AttackVectors.NoTheft
