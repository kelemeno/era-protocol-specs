import EraSpec.Core.Word


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


/-- An abstract IMT leaf: its key and its linked-list successor key. -/
structure AbsLeaf where
  key : UInt256
  nextKey : UInt256
deriving DecidableEq


/-- Every `nextKey` is a sound gap witness: any strictly larger key in the set
is at least `nextKey`, and the existence of one forces `nextKey ≠ 0`. -/
def GapSound (s : Finset AbsLeaf) : Prop :=
  ∀ W ∈ s, ∀ L ∈ s, W.key < L.key → W.nextKey ≠ 0 ∧ W.nextKey ≤ L.key


/-- Keys identify leaves. -/
def KeyInj (s : Finset AbsLeaf) : Prop :=
  ∀ A ∈ s, ∀ B ∈ s, A.key = B.key → A = B


/-- The IMT insert of a new key `v` through the low leaf `W₀`: retarget `W₀`'s
`nextKey` to `v` and add the new leaf `⟨v, W₀.nextKey⟩`. -/
def imtInsert (s : Finset AbsLeaf) (W₀ : AbsLeaf) (v : UInt256) : Finset AbsLeaf :=
  insert ⟨W₀.key, v⟩ (insert ⟨v, W₀.nextKey⟩ (s.erase W₀))


/-! ## The temporal layer — append-only history and the delivered-XOR-reclaimed core

The delivery gate accepts a membership proof against SOME settled root with
`l1Timestamp ≤ deadline`; the reclaim gate accepts a gap witness against the
LAST settled root with `l1Timestamp ≤ deadline`, pinned by a successor root
with `l1Timestamp > deadline`.  With monotone timestamps and a key-set that
only grows (the IMT insert never removes a key — it only retargets a
`nextKey`), both cannot hold for the same commit value. -/

/-- The key set of a leaf set. -/
def keys (s : Finset AbsLeaf) : Finset UInt256 :=
  s.image AbsLeaf.key


/-- An IMT history: each snapshot is the previous one, or an insert of a
fresh key through a well-formed window (exactly the guarded operation the
tree contract performs). -/
def Evolution (S : ℕ → Finset AbsLeaf) : Prop :=
  ∀ n, S (n+1) = S n
    ∨ ∃ W₀ v, W₀ ∈ S n ∧ W₀.key < v ∧ (W₀.nextKey = 0 ∨ v < W₀.nextKey)
        ∧ S (n+1) = imtInsert (S n) W₀ v


/-! ## Reclaim liveness — a gap witness always EXISTS for an absent key

The reclaim gate (#26) demands a leaf whose window straddles the missing
commit value.  The exclusivity results say such a witness is *sound*; this
section says one is always *available*: in a well-formed linked list, the
maximal key below an absent `v` carries a straddling window.  Two more
list invariants make "well-formed" precise, and both are preserved by the
guarded insert. -/

/-- Every nonzero `nextKey` resolves to an actual leaf — no dangling links. -/
def NextClosed (s : Finset AbsLeaf) : Prop :=
  ∀ W ∈ s, W.nextKey ≠ 0 → ∃ L ∈ s, L.key = W.nextKey


/-- Windows open upward: `nextKey` is 0 (list end) or strictly above the key. -/
def WindowPos (s : Finset AbsLeaf) : Prop :=
  ∀ W ∈ s, W.nextKey = 0 ∨ W.key < W.nextKey


/-- The full linked-list well-formedness bundle. -/
def SoundState (s : Finset AbsLeaf) : Prop :=
  GapSound s ∧ KeyInj s ∧ NextClosed s ∧ WindowPos s


/-! ## Representation key-injectivity — hypothesis (iv) made inductive

`image_insert_effect`'s uniqueness hypothesis ("the low leaf is represented
only at the low index") is not free-standing: two indices could in principle
carry identical leaves.  But the concrete tree can't produce that — distinct
indices always hold distinct KEYS, because every insert adds a fresh key and
the retarget keeps its key.  This section closes the loop: `RepKeyInj` is
preserved by the insert step, the freshness it needs follows from the gap
window itself, and uniqueness (iv) is a one-line corollary.  Nothing about
the insert chain remains non-inductive. -/

/-- Distinct indices represent distinct keys. -/
def RepKeyInj {α : Type} (f : α → AbsLeaf) (bases : Finset α) : Prop :=
  ∀ b ∈ bases, ∀ c ∈ bases, (f b).key = (f c).key → b = c


/-! ## The synthetic direction — a concrete guarded history IS an `Evolution`

Every theorem above is *analytic*: assume `Evolution` and derive a security
property.  The concrete contract, however, produces steps guarded only by the
WEAK loop-exit window plus the dedup gate.  `GuardedEvolution` captures exactly
that history shape, and `guardedEvolution_isEvolution` shows it refines to an
`Evolution` — so the entire analytic corpus (`reclaimable_iff_absent`,
exactly-once delivery, the ledgers, `delivered_leg_available_forever`) applies
verbatim to real contract runs from a sound genesis. -/

/-- A history whose every step is a no-op or a guarded concrete insert:
low leaf in the set, strictly below `v`, the WEAK loop-exit window, and the
dedup gate `v ∉ keys`. -/
def GuardedEvolution (S : ℕ → Finset AbsLeaf) : Prop :=
  ∀ n, S (n+1) = S n
    ∨ ∃ (W : AbsLeaf) (v : UInt256),
        W ∈ S n ∧ W.key < v ∧ (W.nextKey = 0 ∨ v ≤ W.nextKey)
          ∧ v ∉ keys (S n) ∧ S (n+1) = imtInsert (S n) W v


end IMTAbstract
