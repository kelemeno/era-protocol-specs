import EraSpec.Contracts.IndexedMerkleTree.Specs.Model

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false


/- EXTRACTED from contracts-formal-verification (`specs/specs/IMTAbstract.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  ABSTRACT INDEXED MERKLE TREE — the sortedness invariant and its consequences.

  An IMT's leaves form a linked list sorted by key: each leaf `⟨key, nextKey⟩`
  points to the next-larger key (`nextKey = 0` on the maximum).  We capture the
  two properties the bridge exclusivity argument needs:

  * `GapSound s` — every leaf's `nextKey` is a *sound gap witness*: whenever
    some leaf has a strictly larger key, `nextKey` is nonzero and a lower bound
    on all strictly-larger keys.  (Equivalently: the open interval
    `(W.key, W.nextKey)` — or `(W.key, ∞)` when `nextKey = 0` — contains no key.)
  * `KeyInj s` — keys are unique identifiers of leaves.

  Results:
  * `gap_excludes_member` — CROSS-POSITION EXCLUSIVITY, abstractly: a leaf
    whose window straddles `v` and a member with key `v` cannot coexist in a
    `GapSound` set.  (The same-position case is #29; this is the other half,
    conditional on the invariant.)
  * `imtInsert_gapSound` / `imtInsert_keyInj` — the IMT INSERT operation
    (retarget the low leaf's `nextKey` to `v`, append `⟨v, oldNext⟩`)
    PRESERVES both properties.  This is the mathematical content the concrete
    `L2InteropCommitmentTree` insert path must implement; with an empty-tree
    base case it gives the invariant for every reachable root by induction.

  Pure order theory — axiom-free, no EVM semantics.
-/

namespace IMTAbstract


open Clear


/-- **CROSS-POSITION EXCLUSIVITY (abstract).**  In a `GapSound` leaf set, an
adjacency leaf `W` whose window straddles `v` (`W.key < v` and `nextKey = 0 ∨
v < nextKey`) excludes ANY member leaf with key `v`. -/
abbrev Properties.gap_excludes_member {s : Finset AbsLeaf} {W L : AbsLeaf} {v : UInt256}
    (hs : GapSound s) (hW : W ∈ s) (hL : L ∈ s)
    (hlow : W.key < v) (hwin : W.nextKey = 0 ∨ v < W.nextKey)
    (hmem : L.key = v) :=
  False


/-- **INSERT PRESERVES `GapSound`.**  Inserting a fresh key `v` through a
well-formed window keeps every gap witness sound. -/
abbrev Properties.imtInsert_gapSound {s : Finset AbsLeaf} {W₀ : AbsLeaf} {v : UInt256}
    (hs : GapSound s) (hinj : KeyInj s) (hW₀ : W₀ ∈ s)
    (hlow : W₀.key < v) (hwin : W₀.nextKey = 0 ∨ v < W₀.nextKey) :=
  GapSound (imtInsert s W₀ v)


/-- **INSERT PRESERVES `KeyInj`.** -/
abbrev Properties.imtInsert_keyInj {s : Finset AbsLeaf} {W₀ : AbsLeaf} {v : UInt256}
    (hs : GapSound s) (hinj : KeyInj s) (hW₀ : W₀ ∈ s)
    (hlow : W₀.key < v) (hwin : W₀.nextKey = 0 ∨ v < W₀.nextKey) :=
  KeyInj (imtInsert s W₀ v)


/-- The IMT insert never removes a key: the erased low leaf is re-added with
the same key (retargeted `nextKey`), and the new leaf only adds `v`. -/
abbrev Properties.imtInsert_keys_grow {s : Finset AbsLeaf} {W₀ : AbsLeaf} {v : UInt256} :=
  keys s ⊆ keys (imtInsert s W₀ v)


/-- **THE INVARIANT IS INDUCTIVE.**  Along any evolution from a `GapSound`,
`KeyInj` base, every snapshot is `GapSound` and `KeyInj`. -/
abbrev Properties.evolution_invariant {S : ℕ → Finset AbsLeaf}
    (hevo : Evolution S) (h0 : GapSound (S 0)) (hinj0 : KeyInj (S 0)) :=
  ∀ n, GapSound (S n) ∧ KeyInj (S n)


/-- Along any evolution, the key set only grows. -/
abbrev Properties.evolution_keys_mono {S : ℕ → Finset AbsLeaf} (hevo : Evolution S) :=
  ∀ {m n : ℕ}, m ≤ n → keys (S m) ⊆ keys (S n)


/-- **DELIVERED XOR RECLAIMED — the temporal core.**  Fix an IMT history `S`
(an `Evolution` from a sound base) with monotone settlement timestamps `t`
and a deadline `D`.  Suppose

* **delivery evidence** for commit value `v`: `v` is a key of some snapshot
  `i` settled on time (`t i ≤ D`) — what the delivery gate (#25) requires of
  every leg; and
* **reclaim evidence** for the same `v`: some snapshot `j` pinned as the last
  on-time one (`D < t (j+1)`) carries a gap witness `W` straddling `v` —
  what the reclaim gate (#26) requires of the missing leg.

Then `False`: the two evidences cannot coexist.  On-time membership persists
to the pinned snapshot (keys only grow, timestamps are monotone so `i ≤ j`),
where the gap witness excludes it (`gap_excludes_member`). -/
abbrev Properties.delivered_and_reclaimed_impossible {S : ℕ → Finset AbsLeaf} {t : ℕ → UInt256} {D v : UInt256}
    (hevo : Evolution S) (h0 : GapSound (S 0)) (hinj0 : KeyInj (S 0))
    (htmono : Monotone t)
    {i : ℕ} (hti : t i ≤ D) (hdel : v ∈ keys (S i))
    {j : ℕ} {W : AbsLeaf} (htj1 : D < t (j+1)) (hW : W ∈ S j)
    (hlow : W.key < v) (hwin : W.nextKey = 0 ∨ v < W.nextKey) :=
  False


/-- The genesis singleton `{⟨0, 0⟩}` (the zero leaf) is a sound base. -/
abbrev Properties.genesis_gapSound :=
  GapSound ({⟨0, 0⟩} : Finset AbsLeaf)


/-- The genesis singleton has unique keys. -/
abbrev Properties.genesis_keyInj :=
  KeyInj ({⟨0, 0⟩} : Finset AbsLeaf)


/-- The empty base is also sound (for trees initialized empty). -/
abbrev Properties.empty_gapSound :=
  GapSound (∅ : Finset AbsLeaf)


/-- The empty base has unique keys. -/
abbrev Properties.empty_keyInj :=
  KeyInj (∅ : Finset AbsLeaf)


/-- **INSERT PRESERVES `NextClosed`.** -/
abbrev Properties.imtInsert_nextClosed {s : Finset AbsLeaf} {W₀ : AbsLeaf} {v : UInt256}
    (hnc : NextClosed s) (hW₀ : W₀ ∈ s)
    (hlow : W₀.key < v) (hwin : W₀.nextKey = 0 ∨ v < W₀.nextKey) :=
  NextClosed (imtInsert s W₀ v)


/-- **INSERT PRESERVES `WindowPos`.** -/
abbrev Properties.imtInsert_windowPos {s : Finset AbsLeaf} {W₀ : AbsLeaf} {v : UInt256}
    (hwp : WindowPos s)
    (hlow : W₀.key < v) (hwin : W₀.nextKey = 0 ∨ v < W₀.nextKey) :=
  WindowPos (imtInsert s W₀ v)


/-- **A GAP WITNESS EXISTS.**  In a well-formed list containing some key
below `v`, an absent `v` always has a straddling window: the leaf with the
MAXIMAL key below `v` carries it. -/
abbrev Properties.gap_witness_exists {s : Finset AbsLeaf} {v : UInt256}
    (hnc : NextClosed s) (hwp : WindowPos s)
    (hbelow : ∃ X ∈ s, X.key < v)
    (habs : v ∉ keys s) :=
  ∃ W ∈ s, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)


/-- **THE FULL INVARIANT IS INDUCTIVE** along any evolution. -/
abbrev Properties.evolution_sound {S : ℕ → Finset AbsLeaf}
    (hevo : Evolution S) (h0 : SoundState (S 0)) :=
  ∀ n, SoundState (S n)


/-- **RECLAIM LIVENESS (abstract).**  Along any evolution from a sound base
containing the zero leaf, EVERY absent nonzero commit value has a valid gap
witness at EVERY snapshot: the reclaim gate can always be satisfied for a
leg that was never committed — at any time, no matter how the tree grew. -/
abbrev Properties.reclaim_witness_available {S : ℕ → Finset AbsLeaf}
    (hevo : Evolution S) (h0 : SoundState (S 0))
    (hzero : (0 : UInt256) ∈ keys (S 0))
    {j : ℕ} {v : UInt256} (hv0 : v ≠ 0) (habs : v ∉ keys (S j)) :=
  ∃ W ∈ S j, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)


/-- **EXACTLY-ONE-OUTCOME CAPSTONE (abstract).**  For a nonzero commit value
`v` that is absent from a deadline-pinned snapshot `j` (`D < t (j+1)`), along
any evolution from a sound base with the zero leaf and monotone settlement
timestamps: a valid RECLAIM witness exists at `j` (never neither — the leg can
be refunded), AND `v` is a key of NO on-time snapshot (never both — the leg
cannot have been delivered).  This is #34 and #35 packaged as the single
"a timed-out leg is reclaimable and not deliverable" statement. -/
abbrev Properties.timed_out_leg_reclaimable_not_deliverable {S : ℕ → Finset AbsLeaf} {t : ℕ → UInt256} {D v : UInt256}
    (hevo : Evolution S) (h0 : SoundState (S 0)) (htmono : Monotone t)
    (hzero : (0 : UInt256) ∈ keys (S 0)) (hv0 : v ≠ 0)
    {j : ℕ} (habs : v ∉ keys (S j)) (htj1 : D < t (j+1)) :=
  (∃ W ∈ S j, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))
        ∧ (∀ i : ℕ, t i ≤ D → v ∉ keys (S i))


/-- **DELIVERED ⇒ NOT RECLAIMABLE (abstract).**  The sharp converse of reclaim
liveness: if commit value `v` IS a key of a snapshot `s` (the leg was delivered —
its leaf is in the tree), then NO leaf of `s` carries a window straddling `v`, so
the reclaim gate's witness precondition (#26) is *unsatisfiable*.  A delivered leg
can never also be refunded — the anti-double-spend guarantee on the reclaim side,
needing only `GapSound` (no timestamps, no evolution). -/
abbrev Properties.present_not_reclaimable {s : Finset AbsLeaf} {v : UInt256}
    (hgs : GapSound s) (hpres : v ∈ keys s) :=
  ¬ ∃ W ∈ s, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)


/-- **RECLAIMABILITY PINS ABSENCE (abstract).**  Combining liveness
(`reclaim_witness_available`) with its converse (`present_not_reclaimable`):
along any evolution from a sound base with the zero leaf, a nonzero commit value
`v` has a valid reclaim witness at snapshot `j` **iff** `v` is absent from `S j`.
So the reclaim gate fires on *exactly* the legs the tree never delivered — no
false refunds, no missed refunds. -/
abbrev Properties.reclaimable_iff_absent {S : ℕ → Finset AbsLeaf}
    (hevo : Evolution S) (h0 : SoundState (S 0))
    (hzero : (0 : UInt256) ∈ keys (S 0))
    {j : ℕ} {v : UInt256} (hv0 : v ≠ 0) :=
  (∃ W ∈ S j, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))
        ↔ v ∉ keys (S j)


/-- The genesis singleton has no dangling links. -/
abbrev Properties.genesis_nextClosed :=
  NextClosed ({⟨0, 0⟩} : Finset AbsLeaf)


/-- The genesis singleton's window opens upward (it is the list end). -/
abbrev Properties.genesis_windowPos :=
  WindowPos ({⟨0, 0⟩} : Finset AbsLeaf)


/-- The genesis singleton is a fully sound base. -/
abbrev Properties.genesis_soundState :=
  SoundState ({⟨0, 0⟩} : Finset AbsLeaf)


/-- The genesis singleton contains the zero key. -/
abbrev Properties.genesis_zero_mem :=
  (0 : UInt256) ∈ keys ({⟨0, 0⟩} : Finset AbsLeaf)


/-! ## The insert-effect bridge — pointwise writes make `imtInsert`

The concrete insert (the dispatcher glue over #39's verified storage
primitives) does three things to the leaves mapping: overwrite the low
leaf's slot triple with the RETARGETED leaf, write the NEW leaf at a fresh
index, and touch nothing else.  This theorem says those pointwise facts —
stated over an abstract representation function `f : index → AbsLeaf` —
force the REPRESENTED SET to transform exactly as `imtInsert`.  It is the
last abstract link: concrete slot arithmetic discharges the four pointwise
hypotheses, and #30/#34/#35 take over from `imtInsert`. -/

/-- **THE INSERT EFFECT.**  If, going from representation `f` to `f'`:
the low index now carries the retargeted leaf `⟨key, v⟩`, the fresh index
carries the new leaf `⟨v, nextKey⟩`, every other index is unchanged, and the
low leaf was uniquely represented — then the image over the grown index set
IS the abstract `imtInsert`. -/
abbrev Properties.image_insert_effect {α : Type} [DecidableEq α]
    {f f' : α → AbsLeaf} {bases : Finset α} {lowb newb : α} {v : UInt256}
    (hnew : newb ∉ bases) (hlow : lowb ∈ bases)
    (hf'low : f' lowb = ⟨(f lowb).key, v⟩)
    (hf'new : f' newb = ⟨v, (f lowb).nextKey⟩)
    (hframe : ∀ b ∈ bases, b ≠ lowb → f' b = f b)
    (huniq : ∀ b ∈ bases, b ≠ lowb → f b ≠ f lowb) :=
  Finset.image f' (insert newb bases)
        = imtInsert (Finset.image f bases) (f lowb) v


/-- **INSERT EFFECT + INVARIANT, in one step.**  The pointwise write facts,
a well-formed window on the represented low leaf, key-injectivity of the old
set, and soundness of the old set give: the NEW represented set is exactly
`imtInsert` AND remains `GapSound`/`KeyInj` — one `Evolution` step. -/
abbrev Properties.image_insert_step {α : Type} [DecidableEq α]
    {f f' : α → AbsLeaf} {bases : Finset α} {lowb newb : α} {v : UInt256}
    (hnew : newb ∉ bases) (hlow : lowb ∈ bases)
    (hf'low : f' lowb = ⟨(f lowb).key, v⟩)
    (hf'new : f' newb = ⟨v, (f lowb).nextKey⟩)
    (hframe : ∀ b ∈ bases, b ≠ lowb → f' b = f b)
    (huniq : ∀ b ∈ bases, b ≠ lowb → f b ≠ f lowb)
    (hgs : GapSound (Finset.image f bases))
    (hinj : KeyInj (Finset.image f bases))
    (hwlow : (f lowb).key < v)
    (hwin : (f lowb).nextKey = 0 ∨ v < (f lowb).nextKey) :=
  Finset.image f' (insert newb bases)
          = imtInsert (Finset.image f bases) (f lowb) v
        ∧ GapSound (Finset.image f' (insert newb bases))
        ∧ KeyInj (Finset.image f' (insert newb bases))


/-- Uniqueness (iv) from representation key-injectivity. -/
abbrev Properties.huniq_of_repKeyInj {α : Type} {f : α → AbsLeaf} {bases : Finset α}
    {lowb : α} (hrki : RepKeyInj f bases) (hlow : lowb ∈ bases) :=
  ∀ b ∈ bases, b ≠ lowb → f b ≠ f lowb


/-- **Freshness is free**: the low leaf's window straddling `v` already
excludes ANY represented key equal to `v` (via `gap_excludes_member`). -/
abbrev Properties.fresh_of_window {α : Type} {f : α → AbsLeaf} {bases : Finset α}
    {lowb : α} {v : UInt256} [DecidableEq α]
    (hgs : GapSound (Finset.image f bases)) (hlow : lowb ∈ bases)
    (hwlow : (f lowb).key < v)
    (hwin : (f lowb).nextKey = 0 ∨ v < (f lowb).nextKey) :=
  ∀ b ∈ bases, (f b).key ≠ v


/-- **THE INSERT STEP PRESERVES `RepKeyInj`**: the retarget keeps its key and
the new index's key `v` is fresh. -/
abbrev Properties.repKeyInj_insert_step {α : Type} [DecidableEq α]
    {f f' : α → AbsLeaf} {bases : Finset α} {lowb newb : α} {v : UInt256}
    (hnew : newb ∉ bases) (hlow : lowb ∈ bases)
    (hf'low : f' lowb = ⟨(f lowb).key, v⟩)
    (hf'new : f' newb = ⟨v, (f lowb).nextKey⟩)
    (hframe : ∀ b ∈ bases, b ≠ lowb → f' b = f b)
    (hrki : RepKeyInj f bases)
    (hfresh : ∀ b ∈ bases, (f b).key ≠ v) :=
  RepKeyInj f' (insert newb bases)


/-- **THE SELF-CONTAINED INDUCTIVE STEP.**  Pointwise write facts + window +
soundness + `RepKeyInj` give: the new set IS `imtInsert`, and ALL THREE
invariants — `GapSound`, `KeyInj`, `RepKeyInj` — carry to the new state.
Uniqueness and freshness are derived, not assumed. -/
abbrev Properties.image_insert_step' {α : Type} [DecidableEq α]
    {f f' : α → AbsLeaf} {bases : Finset α} {lowb newb : α} {v : UInt256}
    (hnew : newb ∉ bases) (hlow : lowb ∈ bases)
    (hf'low : f' lowb = ⟨(f lowb).key, v⟩)
    (hf'new : f' newb = ⟨v, (f lowb).nextKey⟩)
    (hframe : ∀ b ∈ bases, b ≠ lowb → f' b = f b)
    (hrki : RepKeyInj f bases)
    (hgs : GapSound (Finset.image f bases))
    (hinj : KeyInj (Finset.image f bases))
    (hwlow : (f lowb).key < v)
    (hwin : (f lowb).nextKey = 0 ∨ v < (f lowb).nextKey) :=
  Finset.image f' (insert newb bases)
          = imtInsert (Finset.image f bases) (f lowb) v
        ∧ GapSound (Finset.image f' (insert newb bases))
        ∧ KeyInj (Finset.image f' (insert newb bases))
        ∧ RepKeyInj f' (insert newb bases)


/-! ## Exact key-set effect of an insert

`imtInsert_keys_grow` only bounds the key set below (`⊆`).  The following pins
it precisely: an insert adjoins EXACTLY the commit value `v` and nothing else —
the retarget preserves `W₀.key`, the erase removes no key (the low leaf's key
returns on the retargeted leaf), and the sole new key is `v`.  Needs only
`W₀ ∈ s` (no window or injectivity hypothesis). -/

/-- **INSERT ADDS EXACTLY `v`.**  The post-insert key set is the old key set
with `v` adjoined.  Sharpens `imtInsert_keys_grow` from `⊆` to `=`. -/
abbrev Properties.imtInsert_keys_eq {s : Finset AbsLeaf} {W₀ : AbsLeaf} {v : UInt256} (hW₀ : W₀ ∈ s) :=
  keys (imtInsert s W₀ v) = insert v (keys s)


/-- Membership form of `imtInsert_keys_eq`. -/
abbrev Properties.mem_keys_imtInsert {s : Finset AbsLeaf} {W₀ : AbsLeaf} {v k : UInt256} (hW₀ : W₀ ∈ s) :=
  k ∈ keys (imtInsert s W₀ v) ↔ k = v ∨ k ∈ keys s


/-- The inserted commit value is present afterwards — the delivery-side
counterpart to `gap_excludes_member` (which shows an ABSENT value stays
excludable). -/
abbrev Properties.imtInsert_key_mem {s : Finset AbsLeaf} {W₀ : AbsLeaf} {v : UInt256} (hW₀ : W₀ ∈ s) :=
  v ∈ keys (imtInsert s W₀ v)


/-- **Per-step key-set evolution (exact).**  Every evolution step either leaves
the key set unchanged or adjoins exactly one commit value.  Sharpens the
monotone `evolution_keys_mono` to a precise per-step account. -/
abbrev Properties.evolution_step_keys {S : ℕ → Finset AbsLeaf} (hevo : Evolution S) (n : ℕ) :=
  keys (S (n+1)) = keys (S n) ∨ ∃ v, keys (S (n+1)) = insert v (keys (S n))


/-- **KEY PROVENANCE.**  Along any evolution, every key present at step `n` that
was not in the genesis set was *freshly inserted at a definite earlier step* `m`:
it was absent at `m` and the step from `m` to `m+1` adjoined exactly it.  The
inductive companion to `evolution_step_keys`: a delivered commit value has a
well-defined point of entry into the tree. -/
abbrev Properties.evolution_key_origin {S : ℕ → Finset AbsLeaf} {v : UInt256} (hevo : Evolution S) :=
  ∀ n, v ∈ keys (S n) → v ∉ keys (S 0) →
        ∃ m, m < n ∧ v ∉ keys (S m) ∧ keys (S (m+1)) = insert v (keys (S m))


/-- **DELIVERY ⟺ INSERTION (abstract).**  A non-genesis commit value is a key of
snapshot `n` **iff** it was freshly inserted at some earlier step.  The
delivery-side companion to `reclaimable_iff_absent`: presence in the tree is
exactly having a point of entry.  (⇒ is `evolution_key_origin`; ⇐ is forward
persistence via `evolution_keys_mono`.) -/
abbrev Properties.evolution_key_present_iff {S : ℕ → Finset AbsLeaf} {v : UInt256} (hevo : Evolution S)
    (h0 : v ∉ keys (S 0)) (n : ℕ) :=
  v ∈ keys (S n)
        ↔ ∃ m, m < n ∧ v ∉ keys (S m) ∧ keys (S (m+1)) = insert v (keys (S m))


/-- **THE ENTRY STEP IS UNIQUE.**  A commit value is absent then present across
at most one step boundary: once inserted it persists (`evolution_keys_mono`), so
it can be absent only strictly before its single point of entry.  Together with
`evolution_key_origin` this makes provenance a well-defined function — every
delivered value entered the tree at exactly one step. -/
abbrev Properties.evolution_key_origin_unique {S : ℕ → Finset AbsLeaf} {v : UInt256} (hevo : Evolution S) {m₁ m₂ : ℕ}
    (h1 : v ∉ keys (S m₁) ∧ v ∈ keys (S (m₁+1)))
    (h2 : v ∉ keys (S m₂) ∧ v ∈ keys (S (m₂+1))) :=
  m₁ = m₂


/-! ## The delivered-value ledger — who is in the tree, and when they entered

`evolution_step_keys` accounts for one step; these theorems telescope it over a
whole history.  The key set at step `n` decomposes EXACTLY into the genesis keys
plus the per-step increments (`evolution_keys_ledger`), the tree's size is the
genesis size plus the number of effective inserts (`evolution_card_ledger`), and
every non-genesis member has EXACTLY ONE entry step
(`evolution_key_origin_exists_unique`) — indeed the guarded insert operation is
never even PERFORMED twice for the same commit value
(`evolution_insert_unique`). -/

/-- **THE KEY-SET LEDGER.**  The keys at step `n` are exactly the genesis keys
together with every step increment `keys (S (m+1)) \ keys (S m)` for `m < n`:
nothing is in the tree without having entered it. -/
abbrev Properties.evolution_keys_ledger {S : ℕ → Finset AbsLeaf} (hevo : Evolution S) (n : ℕ) :=
  keys (S n)
        = keys (S 0)
          ∪ (Finset.range n).biUnion (fun m => keys (S (m+1)) \ keys (S m))


/-- **THE SIZE LEDGER.**  The number of keys at step `n` is the genesis count
plus the number of EFFECTIVE steps (those that changed the key set) before `n` —
every effective step delivers exactly one new commit value, so tree growth
counts deliveries. -/
abbrev Properties.evolution_card_ledger {S : ℕ → Finset AbsLeaf} (hevo : Evolution S) (n : ℕ) :=
  (keys (S n)).card
        = (keys (S 0)).card
          + ((Finset.range n).filter (fun m => keys (S (m+1)) ≠ keys (S m))).card


/-- **EXACTLY-ONCE DELIVERY (set level).**  A commit value absent at genesis and
present at step `n` has EXACTLY ONE entry step: existence is
`evolution_key_origin`, uniqueness is `evolution_key_origin_unique`.  Provenance
is a total function on delivered values. -/
abbrev Properties.evolution_key_origin_exists_unique {S : ℕ → Finset AbsLeaf} {v : UInt256} (hevo : Evolution S)
    (h0 : v ∉ keys (S 0)) {n : ℕ} (hmem : v ∈ keys (S n)) :=
  ∃! m, m < n ∧ v ∉ keys (S m) ∧ keys (S (m+1)) = insert v (keys (S m))


/-- **THE GUARDED INSERT RUNS AT MOST ONCE PER VALUE.**  Along any evolution from
a sound base, two guarded inserts of the SAME commit value are the SAME step:
each insert's window proves `v` absent just before it
(`present_not_reclaimable`), each makes `v` present just after it
(`imtInsert_key_mem`), and absent-then-present happens at one step boundary only
(`evolution_key_origin_unique`).  No leg can be delivered twice, at the
operation level. -/
abbrev Properties.evolution_insert_unique {S : ℕ → Finset AbsLeaf} {v : UInt256}
    (hevo : Evolution S) (h0 : GapSound (S 0)) (hinj0 : KeyInj (S 0))
    {m₁ m₂ : ℕ} {W₁ W₂ : AbsLeaf}
    (hW₁ : W₁ ∈ S m₁) (hlow₁ : W₁.key < v)
    (hwin₁ : W₁.nextKey = 0 ∨ v < W₁.nextKey)
    (hstep₁ : S (m₁+1) = imtInsert (S m₁) W₁ v)
    (hW₂ : W₂ ∈ S m₂) (hlow₂ : W₂.key < v)
    (hwin₂ : W₂.nextKey = 0 ∨ v < W₂.nextKey)
    (hstep₂ : S (m₂+1) = imtInsert (S m₂) W₂ v) :=
  m₁ = m₂


/-! ## Cross-chain atomicity, abstract core

"Atomicity" in this project means the AtomicFlow's cross-chain guarantee: a
bundle executed on a single chain can be executed on all other chains of the
flow.  In this model the flow's legs share one commitment history `S` (the
interop roots are published to every chain).  A leg executed on chain A
supplies delivery evidence — membership in a snapshot settled on time.  The
composite below is what a sibling chain B needs: that evidence never decays
(membership persists at every later root B may verify against), and no
reclaim witness for the leg can ever be produced (so B's execution can never
be raced by a reclaim).  Per-chain, evidence acceptance is #57's
verified ⇒ executable hook; per-chain re-execution is blocked by #50. -/

/-- **A DELIVERED LEG IS AVAILABLE FOREVER, AND NEVER RECLAIMABLE.**
Delivery evidence for `v` at an on-time snapshot `i` yields (1) membership
at EVERY later snapshot — any chain verifying against any later published
root accepts the same leg — and (2) the impossibility of any reclaim
witness for `v` at any deadline-pinned snapshot, ever. -/
abbrev Properties.delivered_leg_available_forever {S : ℕ → Finset AbsLeaf} {t : ℕ → UInt256} {D v : UInt256}
    (hevo : Evolution S) (h0 : GapSound (S 0)) (hinj0 : KeyInj (S 0))
    (htmono : Monotone t)
    {i : ℕ} (hti : t i ≤ D) (hdel : v ∈ keys (S i)) :=
  (∀ j, i ≤ j → v ∈ keys (S j))
      ∧ (∀ j (W : AbsLeaf), D < t (j+1) → W ∈ S j → W.key < v →
          ¬ (W.nextKey = 0 ∨ v < W.nextKey))


/-- **THE LOOP-EXIT GUARD IS STRICT.**  The concrete insert's search loop
exits with the weak window `nextKey = 0 ∨ v ≤ nextKey`; the dedup gate
(`valueToIndex[v] == 0`, i.e. `v ∉ keys s`) upgrades it to the STRICT window
`Evolution` requires — a nonzero `nextKey` resolves to an actual leaf
(`NextClosed`), so `v = nextKey` would put `v` in the key set. -/
abbrev Properties.window_strict_of_not_mem {s : Finset AbsLeaf} {W : AbsLeaf} {v : UInt256}
    (hclosed : NextClosed s) (hW : W ∈ s)
    (hnot : v ∉ keys s)
    (hwin : W.nextKey = 0 ∨ v ≤ W.nextKey) :=
  W.nextKey = 0 ∨ v < W.nextKey


/-- **THE CONCRETE GUARD IMPLEMENTS ONE SOUND INSERT STEP.**  From a sound
state, the contract's actual loop-exit — the WEAK window `nextKey = 0 ∨
v ≤ nextKey` — together with the dedup gate (`v ∉ keys`) performs a genuine
sound `imtInsert` that adds *exactly* `v`.  Strictness of the window (which
`Evolution`/`imtInsert_*` require) is recovered from the gate via
`window_strict_of_not_mem`, and every invariant of `SoundState` is preserved.
This is the bridge from the concrete insert path to an `Evolution` step:
its two conclusions discharge the `hwin`/soundness premise and the exact
key-set effect an `Evolution` witness must supply. -/
abbrev Properties.guarded_insert_sound_step {s : Finset AbsLeaf} {W : AbsLeaf} {v : UInt256}
    (hs : SoundState s) (hW : W ∈ s)
    (hlow : W.key < v) (hwin : W.nextKey = 0 ∨ v ≤ W.nextKey)
    (hnot : v ∉ keys s) :=
  SoundState (imtInsert s W v) ∧ keys (imtInsert s W v) = insert v (keys s)


/-- **THE GUARDED INSERT TOGGLES RECLAIMABILITY ATOMICALLY.**  At the exact
delivery event, `v` flips from reclaimable to permanently un-reclaimable:
*before* the guarded insert the low leaf `W` is itself a straddling reclaim
witness for the absent `v`; *after* it, `v` is a key of the tree, so — by
`present_not_reclaimable` on the (still sound) result — NO leaf carries a
window straddling `v`.  A leg cannot be both refunded and delivered across
the single step that delivers it: the no-double-spend guarantee localized to
the delivery boundary. -/
abbrev Properties.guarded_insert_toggles_reclaimable {s : Finset AbsLeaf} {W : AbsLeaf} {v : UInt256}
    (hs : SoundState s) (hW : W ∈ s)
    (hlow : W.key < v) (hwin : W.nextKey = 0 ∨ v ≤ W.nextKey)
    (hnot : v ∉ keys s) :=
  (∃ W' ∈ s, W'.key < v ∧ (W'.nextKey = 0 ∨ v < W'.nextKey))
        ∧ ¬ ∃ W' ∈ imtInsert s W v, W'.key < v ∧ (W'.nextKey = 0 ∨ v < W'.nextKey)


/-- A guarded history from a sound genesis stays sound at every step. -/
abbrev Properties.guardedEvolution_sound {S : ℕ → Finset AbsLeaf} (hge : GuardedEvolution S) (h0 : SoundState (S 0)) :=
  ∀ n, SoundState (S n)


/-- **THE CONCRETE GUARD REFINES TO `Evolution`.**  A `GuardedEvolution` from
a sound genesis is an `Evolution`: at each insert step the dedup gate upgrades
the weak window to the strict one (`window_strict_of_not_mem`, discharged
against the step's own sound state).  Bridges every analytic security theorem
to real contract histories. -/
abbrev Properties.guardedEvolution_isEvolution {S : ℕ → Finset AbsLeaf} (hge : GuardedEvolution S) (h0 : SoundState (S 0)) :=
  Evolution S


/-! ## Genesis-rooted capstones — the headline guarantees for real histories

Specializing the analytic theorems to a `GuardedEvolution` from the genesis
singleton `{⟨0,0⟩}`.  These are the statements a concrete `L2InteropCommitmentTree`
run discharges directly: no `Evolution`/`SoundState` obligations survive — the
guard shape and genesis are the only hypotheses (plus timestamp monotonicity for
the delivery statement). -/

/-- **RECLAIM DICHOTOMY FOR REAL HISTORIES.**  Along any guarded history from
genesis, a nonzero commit value `v` has a valid reclaim witness at snapshot `j`
iff `v` is absent from `S j`: the refund gate fires on exactly the legs the tree
never delivered — no false refunds, no missed refunds. -/
abbrev Properties.guardedEvolution_reclaimable_iff_absent {S : ℕ → Finset AbsLeaf} (hge : GuardedEvolution S)
    (hgen : S 0 = ({⟨0, 0⟩} : Finset AbsLeaf))
    {j : ℕ} {v : UInt256} (hv0 : v ≠ 0) :=
  (∃ W ∈ S j, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))
        ↔ v ∉ keys (S j)


/-- **DELIVERY IS FINAL FOR REAL HISTORIES.**  On-time delivery evidence for
`v` at snapshot `i` (of a guarded history from genesis, with monotone settlement
timestamps) persists at every later snapshot AND forecloses every future reclaim
witness for `v`: a delivered leg can never be raced by a refund. -/
abbrev Properties.guardedEvolution_delivered_available_forever {S : ℕ → Finset AbsLeaf} {t : ℕ → UInt256} {D v : UInt256}
    (hge : GuardedEvolution S) (hgen : S 0 = ({⟨0, 0⟩} : Finset AbsLeaf))
    (htmono : Monotone t)
    {i : ℕ} (hti : t i ≤ D) (hdel : v ∈ keys (S i)) :=
  (∀ j, i ≤ j → v ∈ keys (S j))
      ∧ (∀ j (W : AbsLeaf), D < t (j+1) → W ∈ S j → W.key < v →
          ¬ (W.nextKey = 0 ∨ v < W.nextKey))


/-- **DELIVERY IS EXACTLY-ONCE FOR REAL HISTORIES.**  Along any guarded history
from genesis, a nonzero commit value present at step `n` has EXACTLY ONE entry
step — provenance is a total function on delivered values, so no leg is ever
delivered twice.  The third headline guarantee, hypothesized on only the guard
shape + genesis. -/
abbrev Properties.guardedEvolution_delivery_exactly_once {S : ℕ → Finset AbsLeaf} (hge : GuardedEvolution S)
    (hgen : S 0 = ({⟨0, 0⟩} : Finset AbsLeaf))
    {v : UInt256} (hv0 : v ≠ 0) {n : ℕ} (hmem : v ∈ keys (S n)) :=
  ∃! m, m < n ∧ v ∉ keys (S m) ∧ keys (S (m+1)) = insert v (keys (S m))


/-! ## Sharpness — witness MEMBERSHIP is indispensable

`gap_excludes_member` / `present_not_reclaimable` exclude a straddling window
only for a witness that is *in* the leaf set (`W ∈ s`).  That hypothesis is not
decorative: the theorem below exhibits a fully `SoundState` tree in which a
DELIVERED value `v` nonetheless admits a straddling window carried by a
NON-member leaf `⟨0, 0⟩`.  So no invariant on the leaf set alone can save the
reclaim gate — the contract must separately guarantee that a presented low leaf
really is a tree leaf.

This is exactly the forged-non-inclusion attack that the padding-hash fix
addresses: when empty positions are padded with `hashLeaf {0,0,0}`, a *padded*
(non-existent) index verifies as the `⟨0, 0⟩` low leaf, whose window
(`nextKey = 0`) straddles every value — including delivered ones.  Padding
empty positions with a dedicated constant distinct from `hashLeaf {0,0,0}`
is what makes `W ∈ s` discharge-able, and hence what makes the exclusivity
theorems applicable. -/

/-- **THE FORGED-PADDING WITNESS BREAKS EXCLUSIVITY.**  For any nonzero `a`
there is a sound tree (`{⟨0, a⟩, ⟨a, 0⟩}`) in which `a` is delivered, yet the
non-member leaf `⟨0, 0⟩` — the hash-of-`{0,0,0}` padding leaf — carries a window
straddling `a`.  Hence `W ∈ s` in `present_not_reclaimable` cannot be dropped,
and empty-slot padding must be distinguishable from the real zero leaf. -/
abbrev Properties.forged_padding_witness_breaks_exclusivity {a : UInt256} (ha : a ≠ 0) :=
  ∃ (s : Finset AbsLeaf) (v : UInt256) (W : AbsLeaf),
        SoundState s ∧ v ∈ keys s ∧ W ∉ s
          ∧ W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)


end IMTAbstract
