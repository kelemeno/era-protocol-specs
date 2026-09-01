import EraSpec.Word

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

/-- **CROSS-POSITION EXCLUSIVITY (abstract).**  In a `GapSound` leaf set, an
adjacency leaf `W` whose window straddles `v` (`W.key < v` and `nextKey = 0 ∨
v < nextKey`) excludes ANY member leaf with key `v`. -/
theorem gap_excludes_member
    {s : Finset AbsLeaf} {W L : AbsLeaf} {v : UInt256}
    (hs : GapSound s) (hW : W ∈ s) (hL : L ∈ s)
    (hlow : W.key < v) (hwin : W.nextKey = 0 ∨ v < W.nextKey)
    (hmem : L.key = v) : False := by
  obtain ⟨hnz, hle⟩ := hs W hW L hL (by rw [hmem]; exact hlow)
  rcases hwin with h0 | hgt
  · exact hnz h0
  · rw [hmem] at hle
    exact absurd hle (not_le.mpr hgt)

/-- The IMT insert of a new key `v` through the low leaf `W₀`: retarget `W₀`'s
`nextKey` to `v` and add the new leaf `⟨v, W₀.nextKey⟩`. -/
def imtInsert (s : Finset AbsLeaf) (W₀ : AbsLeaf) (v : UInt256) : Finset AbsLeaf :=
  insert ⟨W₀.key, v⟩ (insert ⟨v, W₀.nextKey⟩ (s.erase W₀))

/-- Membership shape of the inserted set. -/
private lemma mem_imtInsert
    {s : Finset AbsLeaf} {W₀ : AbsLeaf} {v : UInt256} {X : AbsLeaf} :
    X ∈ imtInsert s W₀ v
      ↔ X = ⟨W₀.key, v⟩ ∨ X = ⟨v, W₀.nextKey⟩ ∨ (X ∈ s ∧ X ≠ W₀) := by
  unfold imtInsert
  simp only [Finset.mem_insert, Finset.mem_erase]
  tauto

/-- A fresh key: `v` inside `W₀`'s window is no existing key. -/
private lemma window_key_fresh
    {s : Finset AbsLeaf} {W₀ : AbsLeaf} {v : UInt256}
    (hs : GapSound s) (hW₀ : W₀ ∈ s)
    (hlow : W₀.key < v) (hwin : W₀.nextKey = 0 ∨ v < W₀.nextKey) :
    ∀ X ∈ s, X.key ≠ v := by
  intro X hX hXv
  exact gap_excludes_member hs hW₀ hX hlow hwin hXv

/-- `v` is nonzero (it is strictly above a key, and keys are ≥ 0). -/
private lemma window_v_ne_zero {k v : UInt256} (hlow : k < v) : v ≠ 0 := by
  intro h
  rw [h] at hlow
  exact absurd hlow (by simp)

/-- **INSERT PRESERVES `GapSound`.**  Inserting a fresh key `v` through a
well-formed window keeps every gap witness sound. -/
theorem imtInsert_gapSound
    {s : Finset AbsLeaf} {W₀ : AbsLeaf} {v : UInt256}
    (hs : GapSound s) (hinj : KeyInj s) (hW₀ : W₀ ∈ s)
    (hlow : W₀.key < v) (hwin : W₀.nextKey = 0 ∨ v < W₀.nextKey) :
    GapSound (imtInsert s W₀ v) := by
  have hv0 : v ≠ 0 := window_v_ne_zero hlow
  intro W hW L hL hkey
  rw [mem_imtInsert] at hW hL
  rcases hW with rfl | rfl | ⟨hWs, hWne⟩
  · -- W = the retargeted low leaf ⟨W₀.key, v⟩ : need v ≠ 0 ∧ v ≤ L.key
    refine ⟨hv0, ?_⟩
    rcases hL with rfl | rfl | ⟨hLs, _⟩
    · exact absurd hkey (lt_irrefl _)
    · exact le_refl v
    · -- L is an untouched old leaf with W₀.key < L.key
      obtain ⟨hnz, hle⟩ := hs W₀ hW₀ L hLs hkey
      rcases hwin with h0 | hgt
      · exact absurd h0 hnz
      · exact le_of_lt (lt_of_lt_of_le hgt hle)
  · -- W = the new leaf ⟨v, W₀.nextKey⟩ : need W₀.nextKey ≠ 0 ∧ ≤ L.key
    rcases hL with rfl | rfl | ⟨hLs, _⟩
    · -- L = retargeted low leaf: v < W₀.key contradicts the window
      exact absurd (lt_trans hlow hkey) (lt_irrefl _)
    · exact absurd hkey (lt_irrefl _)
    · -- L untouched old leaf with v < L.key; then W₀.key < L.key
      exact hs W₀ hW₀ L hLs (lt_trans hlow hkey)
  · -- W untouched old leaf
    rcases hL with rfl | rfl | ⟨hLs, _⟩
    · -- L = retargeted low leaf (key W₀.key): the old pair (W, W₀) answers
      exact hs W hWs W₀ hW₀ hkey
    · -- L = new leaf (key v): W.key < v
      rcases lt_trichotomy W.key W₀.key with hlt | heq | hgt
      · obtain ⟨hnz, hle⟩ := hs W hWs W₀ hW₀ hlt
        exact ⟨hnz, le_of_lt (lt_of_le_of_lt hle hlow)⟩
      · exact absurd (hinj W hWs W₀ hW₀ heq) hWne
      · -- W₀.key < W.key: the old gap forces W.key ≥ W₀.nextKey > v — contra
        obtain ⟨hnz, hle⟩ := hs W₀ hW₀ W hWs hgt
        rcases hwin with h0 | hgt'
        · exact absurd h0 hnz
        · exact absurd hkey (not_lt.mpr (le_of_lt (lt_of_lt_of_le hgt' hle)))
    · exact hs W hWs L hLs hkey

/-- **INSERT PRESERVES `KeyInj`.** -/
theorem imtInsert_keyInj
    {s : Finset AbsLeaf} {W₀ : AbsLeaf} {v : UInt256}
    (hs : GapSound s) (hinj : KeyInj s) (hW₀ : W₀ ∈ s)
    (hlow : W₀.key < v) (hwin : W₀.nextKey = 0 ∨ v < W₀.nextKey) :
    KeyInj (imtInsert s W₀ v) := by
  have hfresh := window_key_fresh hs hW₀ hlow hwin
  intro A hA B hB hkey
  rw [mem_imtInsert] at hA hB
  rcases hA with rfl | rfl | ⟨hAs, hAne⟩ <;> rcases hB with rfl | rfl | ⟨hBs, hBne⟩
  · rfl
  · -- W₀.key = v contradicts the strict window edge
    exact absurd hkey (ne_of_lt hlow)
  · -- an old leaf shares W₀'s key ⇒ it IS W₀ ⇒ erased
    exact absurd (hinj W₀ hW₀ B hBs hkey).symm hBne
  · exact absurd hkey.symm (ne_of_lt hlow)
  · rfl
  · exact absurd hkey.symm (hfresh B hBs)
  · exact absurd (hinj A hAs W₀ hW₀ hkey) hAne
  · exact absurd hkey (hfresh A hAs)
  · exact hinj A hAs B hBs hkey

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

/-- The IMT insert never removes a key: the erased low leaf is re-added with
the same key (retargeted `nextKey`), and the new leaf only adds `v`. -/
theorem imtInsert_keys_grow
    {s : Finset AbsLeaf} {W₀ : AbsLeaf} {v : UInt256} :
    keys s ⊆ keys (imtInsert s W₀ v) := by
  intro k hk
  obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hk
  by_cases hXW : X = W₀
  · exact Finset.mem_image.mpr ⟨⟨W₀.key, v⟩,
      by rw [mem_imtInsert]; left; rfl,
      by rw [hXW]⟩
  · exact Finset.mem_image.mpr ⟨X,
      by rw [mem_imtInsert]; right; right; exact ⟨hX, hXW⟩,
      rfl⟩

/-- An IMT history: each snapshot is the previous one, or an insert of a
fresh key through a well-formed window (exactly the guarded operation the
tree contract performs). -/
def Evolution (S : ℕ → Finset AbsLeaf) : Prop :=
  ∀ n, S (n+1) = S n
    ∨ ∃ W₀ v, W₀ ∈ S n ∧ W₀.key < v ∧ (W₀.nextKey = 0 ∨ v < W₀.nextKey)
        ∧ S (n+1) = imtInsert (S n) W₀ v

/-- **THE INVARIANT IS INDUCTIVE.**  Along any evolution from a `GapSound`,
`KeyInj` base, every snapshot is `GapSound` and `KeyInj`. -/
theorem evolution_invariant
    {S : ℕ → Finset AbsLeaf}
    (hevo : Evolution S) (h0 : GapSound (S 0)) (hinj0 : KeyInj (S 0)) :
    ∀ n, GapSound (S n) ∧ KeyInj (S n) := by
  intro n
  induction n with
  | zero => exact ⟨h0, hinj0⟩
  | succ n ih =>
    rcases hevo n with heq | ⟨W₀, v, hW₀, hlow, hwin, heq⟩
    · rw [heq]; exact ih
    · rw [heq]
      exact ⟨imtInsert_gapSound ih.1 ih.2 hW₀ hlow hwin,
             imtInsert_keyInj ih.1 ih.2 hW₀ hlow hwin⟩

/-- Along any evolution, the key set only grows. -/
theorem evolution_keys_mono
    {S : ℕ → Finset AbsLeaf} (hevo : Evolution S) :
    ∀ {m n : ℕ}, m ≤ n → keys (S m) ⊆ keys (S n) := by
  intro m n hmn
  induction n with
  | zero =>
    rcases Nat.le_zero.mp hmn with rfl
    exact Finset.Subset.refl _
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hmn with rfl | hlt
    · exact Finset.Subset.refl _
    · have hstep : keys (S n) ⊆ keys (S (n+1)) := by
        rcases hevo n with heq | ⟨W₀, v, _, _, _, heq⟩
        · rw [heq]
        · rw [heq]
          exact imtInsert_keys_grow
      exact Finset.Subset.trans (ih (Nat.lt_succ_iff.mp hlt)) hstep

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
theorem delivered_and_reclaimed_impossible
    {S : ℕ → Finset AbsLeaf} {t : ℕ → UInt256} {D v : UInt256}
    (hevo : Evolution S) (h0 : GapSound (S 0)) (hinj0 : KeyInj (S 0))
    (htmono : Monotone t)
    {i : ℕ} (hti : t i ≤ D) (hdel : v ∈ keys (S i))
    {j : ℕ} {W : AbsLeaf} (htj1 : D < t (j+1)) (hW : W ∈ S j)
    (hlow : W.key < v) (hwin : W.nextKey = 0 ∨ v < W.nextKey) :
    False := by
  have hij : i ≤ j := by
    by_contra hgt
    push_neg at hgt
    exact absurd hti (not_le.mpr (lt_of_lt_of_le htj1 (htmono hgt)))
  have hkeys : v ∈ keys (S j) := evolution_keys_mono hevo hij hdel
  obtain ⟨L, hL, hLkey⟩ := Finset.mem_image.mp hkeys
  exact gap_excludes_member (evolution_invariant hevo h0 hinj0 j).1
    hW hL hlow hwin hLkey

/-- The genesis singleton `{⟨0, 0⟩}` (the zero leaf) is a sound base. -/
theorem genesis_gapSound : GapSound ({⟨0, 0⟩} : Finset AbsLeaf) := by
  intro W hW L hL hlt
  rw [Finset.mem_singleton] at hW hL
  subst hW; subst hL
  exact absurd hlt (lt_irrefl _)

/-- The genesis singleton has unique keys. -/
theorem genesis_keyInj : KeyInj ({⟨0, 0⟩} : Finset AbsLeaf) := by
  intro A hA B hB _
  rw [Finset.mem_singleton] at hA hB
  rw [hA, hB]

/-- The empty base is also sound (for trees initialized empty). -/
theorem empty_gapSound : GapSound (∅ : Finset AbsLeaf) := by
  intro W hW
  exact absurd hW (Finset.not_mem_empty W)

/-- The empty base has unique keys. -/
theorem empty_keyInj : KeyInj (∅ : Finset AbsLeaf) := by
  intro A hA
  exact absurd hA (Finset.not_mem_empty A)

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

/-- **INSERT PRESERVES `NextClosed`.** -/
theorem imtInsert_nextClosed
    {s : Finset AbsLeaf} {W₀ : AbsLeaf} {v : UInt256}
    (hnc : NextClosed s) (hW₀ : W₀ ∈ s)
    (hlow : W₀.key < v) (hwin : W₀.nextKey = 0 ∨ v < W₀.nextKey) :
    NextClosed (imtInsert s W₀ v) := by
  intro W hW hnz
  rw [mem_imtInsert] at hW
  rcases hW with rfl | rfl | ⟨hWs, _⟩
  · -- retargeted low leaf ⟨W₀.key, v⟩: its nextKey v is the new leaf's key
    exact ⟨⟨v, W₀.nextKey⟩, by rw [mem_imtInsert]; right; left; rfl, rfl⟩
  · -- new leaf ⟨v, W₀.nextKey⟩: the old target of W₀ survives the erase
    obtain ⟨L, hLs, hLkey⟩ := hnc W₀ hW₀ hnz
    have hLne : L ≠ W₀ := by
      intro h
      rw [h] at hLkey
      rcases hwin with h0 | hgt
      · exact hnz h0
      · exact absurd hLkey (ne_of_lt (lt_trans hlow hgt))
    exact ⟨L, by rw [mem_imtInsert]; right; right; exact ⟨hLs, hLne⟩, hLkey⟩
  · -- untouched old leaf: its old target either survives, or was W₀ — whose
    -- key is re-added by the retargeted leaf
    obtain ⟨L, hLs, hLkey⟩ := hnc W hWs hnz
    by_cases hLW : L = W₀
    · refine ⟨⟨W₀.key, v⟩, by rw [mem_imtInsert]; left; rfl, ?_⟩
      rw [← hLkey, hLW]
    · exact ⟨L, by rw [mem_imtInsert]; right; right; exact ⟨hLs, hLW⟩, hLkey⟩

/-- **INSERT PRESERVES `WindowPos`.** -/
theorem imtInsert_windowPos
    {s : Finset AbsLeaf} {W₀ : AbsLeaf} {v : UInt256}
    (hwp : WindowPos s)
    (hlow : W₀.key < v) (hwin : W₀.nextKey = 0 ∨ v < W₀.nextKey) :
    WindowPos (imtInsert s W₀ v) := by
  intro W hW
  rw [mem_imtInsert] at hW
  rcases hW with rfl | rfl | ⟨hWs, _⟩
  · exact Or.inr hlow
  · rcases hwin with h0 | hgt
    · exact Or.inl h0
    · exact Or.inr hgt
  · exact hwp W hWs

/-- **A GAP WITNESS EXISTS.**  In a well-formed list containing some key
below `v`, an absent `v` always has a straddling window: the leaf with the
MAXIMAL key below `v` carries it. -/
theorem gap_witness_exists
    {s : Finset AbsLeaf} {v : UInt256}
    (hnc : NextClosed s) (hwp : WindowPos s)
    (hbelow : ∃ X ∈ s, X.key < v)
    (habs : v ∉ keys s) :
    ∃ W ∈ s, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey) := by
  classical
  set B := s.filter (fun X => X.key < v) with hB
  have hBne : B.Nonempty := by
    obtain ⟨X, hXs, hXv⟩ := hbelow
    exact ⟨X, by rw [hB, Finset.mem_filter]; exact ⟨hXs, hXv⟩⟩
  obtain ⟨W, hWB, hWmax⟩ := B.exists_max_image AbsLeaf.key hBne
  have hWB' := hWB
  rw [hB, Finset.mem_filter] at hWB'
  have hWs : W ∈ s := hWB'.1
  have hWv : W.key < v := hWB'.2
  refine ⟨W, hWs, hWv, ?_⟩
  by_cases h0 : W.nextKey = 0
  · exact Or.inl h0
  · right
    -- the link target is a real leaf strictly above W.key
    obtain ⟨L, hLs, hLkey⟩ := hnc W hWs h0
    have hgt : W.key < W.nextKey := by
      rcases hwp W hWs with h | h
      · exact absurd h h0
      · exact h
    rcases lt_trichotomy W.nextKey v with hlt | heq | hgt'
    · -- target below v: it beats W's maximality
      have hLB : L ∈ B := by
        rw [hB, Finset.mem_filter]
        exact ⟨hLs, by rw [hLkey]; exact hlt⟩
      have := hWmax L hLB
      rw [hLkey] at this
      exact absurd this (not_le.mpr hgt)
    · -- target IS v: contradicts absence
      exact absurd (Finset.mem_image.mpr ⟨L, hLs, by rw [hLkey, heq]⟩) habs
    · exact hgt'

/-- The full linked-list well-formedness bundle. -/
def SoundState (s : Finset AbsLeaf) : Prop :=
  GapSound s ∧ KeyInj s ∧ NextClosed s ∧ WindowPos s

/-- **THE FULL INVARIANT IS INDUCTIVE** along any evolution. -/
theorem evolution_sound
    {S : ℕ → Finset AbsLeaf}
    (hevo : Evolution S) (h0 : SoundState (S 0)) :
    ∀ n, SoundState (S n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    obtain ⟨hgs, hinj, hnc, hwp⟩ := ih
    rcases hevo n with heq | ⟨W₀, v, hW₀, hlow, hwin, heq⟩
    · rw [heq]; exact ⟨hgs, hinj, hnc, hwp⟩
    · rw [heq]
      exact ⟨imtInsert_gapSound hgs hinj hW₀ hlow hwin,
             imtInsert_keyInj hgs hinj hW₀ hlow hwin,
             imtInsert_nextClosed hnc hW₀ hlow hwin,
             imtInsert_windowPos hwp hlow hwin⟩

/-- **RECLAIM LIVENESS (abstract).**  Along any evolution from a sound base
containing the zero leaf, EVERY absent nonzero commit value has a valid gap
witness at EVERY snapshot: the reclaim gate can always be satisfied for a
leg that was never committed — at any time, no matter how the tree grew. -/
theorem reclaim_witness_available
    {S : ℕ → Finset AbsLeaf}
    (hevo : Evolution S) (h0 : SoundState (S 0))
    (hzero : (0 : UInt256) ∈ keys (S 0))
    {j : ℕ} {v : UInt256} (hv0 : v ≠ 0) (habs : v ∉ keys (S j)) :
    ∃ W ∈ S j, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey) := by
  obtain ⟨_, _, hnc, hwp⟩ := evolution_sound hevo h0 j
  have hzeroj : (0 : UInt256) ∈ keys (S j) :=
    evolution_keys_mono hevo (Nat.zero_le j) hzero
  obtain ⟨Z, hZs, hZkey⟩ := Finset.mem_image.mp hzeroj
  refine gap_witness_exists hnc hwp ⟨Z, hZs, ?_⟩ habs
  rw [hZkey]
  exact Fin.pos_of_ne_zero hv0

/-- **EXACTLY-ONE-OUTCOME CAPSTONE (abstract).**  For a nonzero commit value
`v` that is absent from a deadline-pinned snapshot `j` (`D < t (j+1)`), along
any evolution from a sound base with the zero leaf and monotone settlement
timestamps: a valid RECLAIM witness exists at `j` (never neither — the leg can
be refunded), AND `v` is a key of NO on-time snapshot (never both — the leg
cannot have been delivered).  This is #34 and #35 packaged as the single
"a timed-out leg is reclaimable and not deliverable" statement. -/
theorem timed_out_leg_reclaimable_not_deliverable
    {S : ℕ → Finset AbsLeaf} {t : ℕ → UInt256} {D v : UInt256}
    (hevo : Evolution S) (h0 : SoundState (S 0)) (htmono : Monotone t)
    (hzero : (0 : UInt256) ∈ keys (S 0)) (hv0 : v ≠ 0)
    {j : ℕ} (habs : v ∉ keys (S j)) (htj1 : D < t (j+1)) :
    (∃ W ∈ S j, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))
      ∧ (∀ i : ℕ, t i ≤ D → v ∉ keys (S i)) := by
  have hgs0 : GapSound (S 0) := h0.1
  have hinj0 : KeyInj (S 0) := h0.2.1
  have hwit := reclaim_witness_available hevo h0 hzero hv0 habs
  refine ⟨hwit, ?_⟩
  intro i hti hmem
  obtain ⟨W, hWj, hlow, hwin⟩ := hwit
  exact delivered_and_reclaimed_impossible hevo hgs0 hinj0 htmono hti hmem htj1 hWj hlow hwin

/-- **DELIVERED ⇒ NOT RECLAIMABLE (abstract).**  The sharp converse of reclaim
liveness: if commit value `v` IS a key of a snapshot `s` (the leg was delivered —
its leaf is in the tree), then NO leaf of `s` carries a window straddling `v`, so
the reclaim gate's witness precondition (#26) is *unsatisfiable*.  A delivered leg
can never also be refunded — the anti-double-spend guarantee on the reclaim side,
needing only `GapSound` (no timestamps, no evolution). -/
theorem present_not_reclaimable
    {s : Finset AbsLeaf} {v : UInt256}
    (hgs : GapSound s) (hpres : v ∈ keys s) :
    ¬ ∃ W ∈ s, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey) := by
  rintro ⟨W, hW, hlow, hwin⟩
  obtain ⟨L, hL, hLkey⟩ := Finset.mem_image.mp hpres
  exact gap_excludes_member hgs hW hL hlow hwin hLkey

/-- **RECLAIMABILITY PINS ABSENCE (abstract).**  Combining liveness
(`reclaim_witness_available`) with its converse (`present_not_reclaimable`):
along any evolution from a sound base with the zero leaf, a nonzero commit value
`v` has a valid reclaim witness at snapshot `j` **iff** `v` is absent from `S j`.
So the reclaim gate fires on *exactly* the legs the tree never delivered — no
false refunds, no missed refunds. -/
theorem reclaimable_iff_absent
    {S : ℕ → Finset AbsLeaf}
    (hevo : Evolution S) (h0 : SoundState (S 0))
    (hzero : (0 : UInt256) ∈ keys (S 0))
    {j : ℕ} {v : UInt256} (hv0 : v ≠ 0) :
    (∃ W ∈ S j, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))
      ↔ v ∉ keys (S j) := by
  constructor
  · intro hwit hpres
    exact present_not_reclaimable (evolution_sound hevo h0 j).1 hpres hwit
  · intro habs
    exact reclaim_witness_available hevo h0 hzero hv0 habs

/-- The genesis singleton has no dangling links. -/
theorem genesis_nextClosed : NextClosed ({⟨0, 0⟩} : Finset AbsLeaf) := by
  intro W hW hnz
  rw [Finset.mem_singleton] at hW
  rw [hW] at hnz
  exact absurd rfl hnz

/-- The genesis singleton's window opens upward (it is the list end). -/
theorem genesis_windowPos : WindowPos ({⟨0, 0⟩} : Finset AbsLeaf) := by
  intro W hW
  rw [Finset.mem_singleton] at hW
  rw [hW]
  exact Or.inl rfl

/-- The genesis singleton is a fully sound base. -/
theorem genesis_soundState : SoundState ({⟨0, 0⟩} : Finset AbsLeaf) :=
  ⟨genesis_gapSound, genesis_keyInj, genesis_nextClosed, genesis_windowPos⟩

/-- The genesis singleton contains the zero key. -/
theorem genesis_zero_mem : (0 : UInt256) ∈ keys ({⟨0, 0⟩} : Finset AbsLeaf) :=
  Finset.mem_image.mpr ⟨⟨0, 0⟩, Finset.mem_singleton_self _, rfl⟩

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
theorem image_insert_effect
    {α : Type} [DecidableEq α]
    {f f' : α → AbsLeaf} {bases : Finset α} {lowb newb : α} {v : UInt256}
    (hnew : newb ∉ bases) (hlow : lowb ∈ bases)
    (hf'low : f' lowb = ⟨(f lowb).key, v⟩)
    (hf'new : f' newb = ⟨v, (f lowb).nextKey⟩)
    (hframe : ∀ b ∈ bases, b ≠ lowb → f' b = f b)
    (huniq : ∀ b ∈ bases, b ≠ lowb → f b ≠ f lowb) :
    Finset.image f' (insert newb bases)
      = imtInsert (Finset.image f bases) (f lowb) v := by
  ext x
  rw [mem_imtInsert, Finset.mem_image]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · right; left
      exact hf'new
    · by_cases hbl : b = lowb
      · subst hbl
        left
        exact hf'low
      · rw [hframe b hb hbl]
        right; right
        exact ⟨Finset.mem_image.mpr ⟨b, hb, rfl⟩, huniq b hb hbl⟩
  · rintro (rfl | rfl | ⟨hx, hne⟩)
    · exact ⟨lowb, Finset.mem_insert.mpr (Or.inr hlow), hf'low⟩
    · exact ⟨newb, Finset.mem_insert_self _ _, hf'new⟩
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
      have hbl : b ≠ lowb := fun h => hne (by rw [h])
      exact ⟨b, Finset.mem_insert.mpr (Or.inr hb), hframe b hb hbl⟩

/-- **INSERT EFFECT + INVARIANT, in one step.**  The pointwise write facts,
a well-formed window on the represented low leaf, key-injectivity of the old
set, and soundness of the old set give: the NEW represented set is exactly
`imtInsert` AND remains `GapSound`/`KeyInj` — one `Evolution` step. -/
theorem image_insert_step
    {α : Type} [DecidableEq α]
    {f f' : α → AbsLeaf} {bases : Finset α} {lowb newb : α} {v : UInt256}
    (hnew : newb ∉ bases) (hlow : lowb ∈ bases)
    (hf'low : f' lowb = ⟨(f lowb).key, v⟩)
    (hf'new : f' newb = ⟨v, (f lowb).nextKey⟩)
    (hframe : ∀ b ∈ bases, b ≠ lowb → f' b = f b)
    (huniq : ∀ b ∈ bases, b ≠ lowb → f b ≠ f lowb)
    (hgs : GapSound (Finset.image f bases))
    (hinj : KeyInj (Finset.image f bases))
    (hwlow : (f lowb).key < v)
    (hwin : (f lowb).nextKey = 0 ∨ v < (f lowb).nextKey) :
    Finset.image f' (insert newb bases)
        = imtInsert (Finset.image f bases) (f lowb) v
      ∧ GapSound (Finset.image f' (insert newb bases))
      ∧ KeyInj (Finset.image f' (insert newb bases)) := by
  have heff := image_insert_effect hnew hlow hf'low hf'new hframe huniq
  have hmem : f lowb ∈ Finset.image f bases :=
    Finset.mem_image.mpr ⟨lowb, hlow, rfl⟩
  refine ⟨heff, ?_, ?_⟩
  · rw [heff]
    exact imtInsert_gapSound hgs hinj hmem hwlow hwin
  · rw [heff]
    exact imtInsert_keyInj hgs hinj hmem hwlow hwin

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

/-- Uniqueness (iv) from representation key-injectivity. -/
theorem huniq_of_repKeyInj {α : Type} {f : α → AbsLeaf} {bases : Finset α}
    {lowb : α} (hrki : RepKeyInj f bases) (hlow : lowb ∈ bases) :
    ∀ b ∈ bases, b ≠ lowb → f b ≠ f lowb :=
  fun b hb hne hfe => hne (hrki b hb lowb hlow (congrArg AbsLeaf.key hfe))

/-- **Freshness is free**: the low leaf's window straddling `v` already
excludes ANY represented key equal to `v` (via `gap_excludes_member`). -/
theorem fresh_of_window {α : Type} {f : α → AbsLeaf} {bases : Finset α}
    {lowb : α} {v : UInt256} [DecidableEq α]
    (hgs : GapSound (Finset.image f bases)) (hlow : lowb ∈ bases)
    (hwlow : (f lowb).key < v)
    (hwin : (f lowb).nextKey = 0 ∨ v < (f lowb).nextKey) :
    ∀ b ∈ bases, (f b).key ≠ v :=
  fun b hb hkey => gap_excludes_member hgs
    (Finset.mem_image.mpr ⟨lowb, hlow, rfl⟩)
    (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
    hwlow hwin hkey

/-- **THE INSERT STEP PRESERVES `RepKeyInj`**: the retarget keeps its key and
the new index's key `v` is fresh. -/
theorem repKeyInj_insert_step {α : Type} [DecidableEq α]
    {f f' : α → AbsLeaf} {bases : Finset α} {lowb newb : α} {v : UInt256}
    (hnew : newb ∉ bases) (hlow : lowb ∈ bases)
    (hf'low : f' lowb = ⟨(f lowb).key, v⟩)
    (hf'new : f' newb = ⟨v, (f lowb).nextKey⟩)
    (hframe : ∀ b ∈ bases, b ≠ lowb → f' b = f b)
    (hrki : RepKeyInj f bases)
    (hfresh : ∀ b ∈ bases, (f b).key ≠ v) :
    RepKeyInj f' (insert newb bases) := by
  -- every old index keeps its key
  have hkey_eq : ∀ b ∈ bases, (f' b).key = (f b).key := by
    intro b hb
    by_cases hbl : b = lowb
    · subst hbl
      rw [hf'low]
    · rw [hframe b hb hbl]
  intro b hb c hc hkey
  rw [Finset.mem_insert] at hb hc
  rcases hb with rfl | hb <;> rcases hc with rfl | hc
  · rfl
  · -- b = newb, c old: key v = old key — contradicts freshness
    rw [hf'new, hkey_eq c hc] at hkey
    exact absurd hkey.symm (hfresh c hc)
  · rw [hf'new, hkey_eq b hb] at hkey
    exact absurd hkey (hfresh b hb)
  · exact hrki b hb c hc (by rw [← hkey_eq b hb, ← hkey_eq c hc]; exact hkey)

/-- **THE SELF-CONTAINED INDUCTIVE STEP.**  Pointwise write facts + window +
soundness + `RepKeyInj` give: the new set IS `imtInsert`, and ALL THREE
invariants — `GapSound`, `KeyInj`, `RepKeyInj` — carry to the new state.
Uniqueness and freshness are derived, not assumed. -/
theorem image_insert_step'
    {α : Type} [DecidableEq α]
    {f f' : α → AbsLeaf} {bases : Finset α} {lowb newb : α} {v : UInt256}
    (hnew : newb ∉ bases) (hlow : lowb ∈ bases)
    (hf'low : f' lowb = ⟨(f lowb).key, v⟩)
    (hf'new : f' newb = ⟨v, (f lowb).nextKey⟩)
    (hframe : ∀ b ∈ bases, b ≠ lowb → f' b = f b)
    (hrki : RepKeyInj f bases)
    (hgs : GapSound (Finset.image f bases))
    (hinj : KeyInj (Finset.image f bases))
    (hwlow : (f lowb).key < v)
    (hwin : (f lowb).nextKey = 0 ∨ v < (f lowb).nextKey) :
    Finset.image f' (insert newb bases)
        = imtInsert (Finset.image f bases) (f lowb) v
      ∧ GapSound (Finset.image f' (insert newb bases))
      ∧ KeyInj (Finset.image f' (insert newb bases))
      ∧ RepKeyInj f' (insert newb bases) := by
  have huniq := huniq_of_repKeyInj hrki hlow
  have hfresh := fresh_of_window hgs hlow hwlow hwin
  obtain ⟨heff, hgs', hinj'⟩ :=
    image_insert_step hnew hlow hf'low hf'new hframe huniq hgs hinj hwlow hwin
  exact ⟨heff, hgs', hinj',
    repKeyInj_insert_step hnew hlow hf'low hf'new hframe hrki hfresh⟩

/-! ## Exact key-set effect of an insert

`imtInsert_keys_grow` only bounds the key set below (`⊆`).  The following pins
it precisely: an insert adjoins EXACTLY the commit value `v` and nothing else —
the retarget preserves `W₀.key`, the erase removes no key (the low leaf's key
returns on the retargeted leaf), and the sole new key is `v`.  Needs only
`W₀ ∈ s` (no window or injectivity hypothesis). -/

/-- **INSERT ADDS EXACTLY `v`.**  The post-insert key set is the old key set
with `v` adjoined.  Sharpens `imtInsert_keys_grow` from `⊆` to `=`. -/
theorem imtInsert_keys_eq
    {s : Finset AbsLeaf} {W₀ : AbsLeaf} {v : UInt256} (hW₀ : W₀ ∈ s) :
    keys (imtInsert s W₀ v) = insert v (keys s) := by
  ext k
  unfold keys
  simp only [Finset.mem_image, Finset.mem_insert]
  constructor
  · rintro ⟨X, hX, rfl⟩
    rw [mem_imtInsert] at hX
    rcases hX with rfl | rfl | ⟨hXs, _⟩
    · exact Or.inr ⟨W₀, hW₀, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨X, hXs, rfl⟩
  · rintro (rfl | ⟨X, hXs, rfl⟩)
    · exact ⟨⟨_, W₀.nextKey⟩, by rw [mem_imtInsert]; exact Or.inr (Or.inl rfl), rfl⟩
    · by_cases hXW : X = W₀
      · exact ⟨⟨W₀.key, v⟩, by rw [mem_imtInsert]; exact Or.inl rfl, by rw [hXW]⟩
      · exact ⟨X, by rw [mem_imtInsert]; exact Or.inr (Or.inr ⟨hXs, hXW⟩), rfl⟩

/-- Membership form of `imtInsert_keys_eq`. -/
theorem mem_keys_imtInsert
    {s : Finset AbsLeaf} {W₀ : AbsLeaf} {v k : UInt256} (hW₀ : W₀ ∈ s) :
    k ∈ keys (imtInsert s W₀ v) ↔ k = v ∨ k ∈ keys s := by
  rw [imtInsert_keys_eq hW₀, Finset.mem_insert]

/-- The inserted commit value is present afterwards — the delivery-side
counterpart to `gap_excludes_member` (which shows an ABSENT value stays
excludable). -/
theorem imtInsert_key_mem
    {s : Finset AbsLeaf} {W₀ : AbsLeaf} {v : UInt256} (hW₀ : W₀ ∈ s) :
    v ∈ keys (imtInsert s W₀ v) := by
  rw [imtInsert_keys_eq hW₀]; exact Finset.mem_insert_self _ _

/-- **Per-step key-set evolution (exact).**  Every evolution step either leaves
the key set unchanged or adjoins exactly one commit value.  Sharpens the
monotone `evolution_keys_mono` to a precise per-step account. -/
theorem evolution_step_keys
    {S : ℕ → Finset AbsLeaf} (hevo : Evolution S) (n : ℕ) :
    keys (S (n+1)) = keys (S n) ∨ ∃ v, keys (S (n+1)) = insert v (keys (S n)) := by
  rcases hevo n with heq | ⟨W₀, v, hW₀, _, _, heq⟩
  · exact Or.inl (by rw [heq])
  · exact Or.inr ⟨v, by rw [heq, imtInsert_keys_eq hW₀]⟩

/-- **KEY PROVENANCE.**  Along any evolution, every key present at step `n` that
was not in the genesis set was *freshly inserted at a definite earlier step* `m`:
it was absent at `m` and the step from `m` to `m+1` adjoined exactly it.  The
inductive companion to `evolution_step_keys`: a delivered commit value has a
well-defined point of entry into the tree. -/
theorem evolution_key_origin
    {S : ℕ → Finset AbsLeaf} {v : UInt256} (hevo : Evolution S) :
    ∀ n, v ∈ keys (S n) → v ∉ keys (S 0) →
      ∃ m, m < n ∧ v ∉ keys (S m) ∧ keys (S (m+1)) = insert v (keys (S m)) := by
  intro n
  induction n with
  | zero => intro hmem h0; exact absurd hmem h0
  | succ n ih =>
    intro hmem h0
    rcases evolution_step_keys hevo n with heq | ⟨w, hw⟩
    · have hvn : v ∈ keys (S n) := by rw [← heq]; exact hmem
      obtain ⟨m, hmn, hnm, hstep⟩ := ih hvn h0
      exact ⟨m, Nat.lt_succ_of_lt hmn, hnm, hstep⟩
    · by_cases hvn : v ∈ keys (S n)
      · obtain ⟨m, hmn, hnm, hstep⟩ := ih hvn h0
        exact ⟨m, Nat.lt_succ_of_lt hmn, hnm, hstep⟩
      · rw [hw] at hmem
        rcases Finset.mem_insert.mp hmem with rfl | hcontra
        · exact ⟨n, Nat.lt_succ_self n, hvn, hw⟩
        · exact absurd hcontra hvn

/-- **DELIVERY ⟺ INSERTION (abstract).**  A non-genesis commit value is a key of
snapshot `n` **iff** it was freshly inserted at some earlier step.  The
delivery-side companion to `reclaimable_iff_absent`: presence in the tree is
exactly having a point of entry.  (⇒ is `evolution_key_origin`; ⇐ is forward
persistence via `evolution_keys_mono`.) -/
theorem evolution_key_present_iff
    {S : ℕ → Finset AbsLeaf} {v : UInt256} (hevo : Evolution S)
    (h0 : v ∉ keys (S 0)) (n : ℕ) :
    v ∈ keys (S n)
      ↔ ∃ m, m < n ∧ v ∉ keys (S m) ∧ keys (S (m+1)) = insert v (keys (S m)) := by
  constructor
  · intro hmem; exact evolution_key_origin hevo n hmem h0
  · rintro ⟨m, hmn, _, hstep⟩
    have hvm1 : v ∈ keys (S (m+1)) := by rw [hstep]; exact Finset.mem_insert_self _ _
    exact evolution_keys_mono hevo (Nat.succ_le_of_lt hmn) hvm1

/-- **THE ENTRY STEP IS UNIQUE.**  A commit value is absent then present across
at most one step boundary: once inserted it persists (`evolution_keys_mono`), so
it can be absent only strictly before its single point of entry.  Together with
`evolution_key_origin` this makes provenance a well-defined function — every
delivered value entered the tree at exactly one step. -/
theorem evolution_key_origin_unique
    {S : ℕ → Finset AbsLeaf} {v : UInt256} (hevo : Evolution S) {m₁ m₂ : ℕ}
    (h1 : v ∉ keys (S m₁) ∧ v ∈ keys (S (m₁+1)))
    (h2 : v ∉ keys (S m₂) ∧ v ∈ keys (S (m₂+1))) :
    m₁ = m₂ := by
  rcases lt_trichotomy m₁ m₂ with hlt | heq | hgt
  · exact absurd (evolution_keys_mono hevo (Nat.succ_le_of_lt hlt) h1.2) h2.1
  · exact heq
  · exact absurd (evolution_keys_mono hevo (Nat.succ_le_of_lt hgt) h2.2) h1.1

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
theorem evolution_keys_ledger
    {S : ℕ → Finset AbsLeaf} (hevo : Evolution S) (n : ℕ) :
    keys (S n)
      = keys (S 0)
        ∪ (Finset.range n).biUnion (fun m => keys (S (m+1)) \ keys (S m)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsub : keys (S n) ⊆ keys (S (n+1)) :=
      evolution_keys_mono hevo (Nat.le_succ n)
    have hdecomp : keys (S n) ∪ (keys (S (n+1)) \ keys (S n)) = keys (S (n+1)) := by
      ext k
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (hk | ⟨hk, _⟩)
        · exact hsub hk
        · exact hk
      · intro hk
        by_cases h : k ∈ keys (S n)
        · exact Or.inl h
        · exact Or.inr ⟨hk, h⟩
    calc keys (S (n+1))
        = keys (S n) ∪ (keys (S (n+1)) \ keys (S n)) := hdecomp.symm
      _ = (keys (S 0) ∪ (Finset.range n).biUnion (fun m => keys (S (m+1)) \ keys (S m)))
            ∪ (keys (S (n+1)) \ keys (S n)) := by rw [ih]
      _ = keys (S 0)
            ∪ ((keys (S (n+1)) \ keys (S n))
                ∪ (Finset.range n).biUnion (fun m => keys (S (m+1)) \ keys (S m))) := by
          rw [Finset.union_assoc,
            Finset.union_comm
              ((Finset.range n).biUnion fun m => keys (S (m+1)) \ keys (S m))
              (keys (S (n+1)) \ keys (S n))]
      _ = keys (S 0)
            ∪ (Finset.range (n+1)).biUnion (fun m => keys (S (m+1)) \ keys (S m)) := by
          rw [Finset.range_succ, Finset.biUnion_insert]

/-- **THE SIZE LEDGER.**  The number of keys at step `n` is the genesis count
plus the number of EFFECTIVE steps (those that changed the key set) before `n` —
every effective step delivers exactly one new commit value, so tree growth
counts deliveries. -/
theorem evolution_card_ledger
    {S : ℕ → Finset AbsLeaf} (hevo : Evolution S) (n : ℕ) :
    (keys (S n)).card
      = (keys (S 0)).card
        + ((Finset.range n).filter (fun m => keys (S (m+1)) ≠ keys (S m))).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_succ, Finset.filter_insert]
    by_cases hch : keys (S (n+1)) ≠ keys (S n)
    · rw [if_pos hch,
        Finset.card_insert_of_not_mem
          (fun h => absurd (Finset.mem_filter.mp h).1 Finset.not_mem_range_self)]
      have hcard : (keys (S (n+1))).card = (keys (S n)).card + 1 := by
        rcases evolution_step_keys hevo n with heq | ⟨v, hv⟩
        · exact absurd heq hch
        · have hvnot : v ∉ keys (S n) := fun hmem =>
            hch (by rw [hv]; exact Finset.insert_eq_self.mpr hmem)
          rw [hv, Finset.card_insert_of_not_mem hvnot]
      rw [hcard, ih]
      omega
    · rw [if_neg hch]
      push_neg at hch
      rw [hch]
      exact ih

/-- **EXACTLY-ONCE DELIVERY (set level).**  A commit value absent at genesis and
present at step `n` has EXACTLY ONE entry step: existence is
`evolution_key_origin`, uniqueness is `evolution_key_origin_unique`.  Provenance
is a total function on delivered values. -/
theorem evolution_key_origin_exists_unique
    {S : ℕ → Finset AbsLeaf} {v : UInt256} (hevo : Evolution S)
    (h0 : v ∉ keys (S 0)) {n : ℕ} (hmem : v ∈ keys (S n)) :
    ∃! m, m < n ∧ v ∉ keys (S m) ∧ keys (S (m+1)) = insert v (keys (S m)) := by
  obtain ⟨m, hmn, habs, hstep⟩ := evolution_key_origin hevo n hmem h0
  refine ⟨m, ⟨hmn, habs, hstep⟩, ?_⟩
  rintro m' ⟨_, habs', hstep'⟩
  exact evolution_key_origin_unique hevo
    ⟨habs', by rw [hstep']; exact Finset.mem_insert_self _ _⟩
    ⟨habs, by rw [hstep]; exact Finset.mem_insert_self _ _⟩

/-- **THE GUARDED INSERT RUNS AT MOST ONCE PER VALUE.**  Along any evolution from
a sound base, two guarded inserts of the SAME commit value are the SAME step:
each insert's window proves `v` absent just before it
(`present_not_reclaimable`), each makes `v` present just after it
(`imtInsert_key_mem`), and absent-then-present happens at one step boundary only
(`evolution_key_origin_unique`).  No leg can be delivered twice, at the
operation level. -/
theorem evolution_insert_unique
    {S : ℕ → Finset AbsLeaf} {v : UInt256}
    (hevo : Evolution S) (h0 : GapSound (S 0)) (hinj0 : KeyInj (S 0))
    {m₁ m₂ : ℕ} {W₁ W₂ : AbsLeaf}
    (hW₁ : W₁ ∈ S m₁) (hlow₁ : W₁.key < v)
    (hwin₁ : W₁.nextKey = 0 ∨ v < W₁.nextKey)
    (hstep₁ : S (m₁+1) = imtInsert (S m₁) W₁ v)
    (hW₂ : W₂ ∈ S m₂) (hlow₂ : W₂.key < v)
    (hwin₂ : W₂.nextKey = 0 ∨ v < W₂.nextKey)
    (hstep₂ : S (m₂+1) = imtInsert (S m₂) W₂ v) :
    m₁ = m₂ := by
  have habs : ∀ m (W : AbsLeaf), W ∈ S m → W.key < v →
      (W.nextKey = 0 ∨ v < W.nextKey) → v ∉ keys (S m) := by
    intro m W hW hlow hwin hmem
    exact present_not_reclaimable (evolution_invariant hevo h0 hinj0 m).1 hmem
      ⟨W, hW, hlow, hwin⟩
  exact evolution_key_origin_unique hevo
    ⟨habs m₁ W₁ hW₁ hlow₁ hwin₁, by rw [hstep₁]; exact imtInsert_key_mem hW₁⟩
    ⟨habs m₂ W₂ hW₂ hlow₂ hwin₂, by rw [hstep₂]; exact imtInsert_key_mem hW₂⟩

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
theorem delivered_leg_available_forever
    {S : ℕ → Finset AbsLeaf} {t : ℕ → UInt256} {D v : UInt256}
    (hevo : Evolution S) (h0 : GapSound (S 0)) (hinj0 : KeyInj (S 0))
    (htmono : Monotone t)
    {i : ℕ} (hti : t i ≤ D) (hdel : v ∈ keys (S i)) :
    (∀ j, i ≤ j → v ∈ keys (S j))
    ∧ (∀ j (W : AbsLeaf), D < t (j+1) → W ∈ S j → W.key < v →
        ¬ (W.nextKey = 0 ∨ v < W.nextKey)) := by
  refine ⟨fun j hij => evolution_keys_mono hevo hij hdel, ?_⟩
  intro j W htj1 hW hlow hwin
  exact delivered_and_reclaimed_impossible hevo h0 hinj0 htmono hti hdel
    htj1 hW hlow hwin

/-- **THE LOOP-EXIT GUARD IS STRICT.**  The concrete insert's search loop
exits with the weak window `nextKey = 0 ∨ v ≤ nextKey`; the dedup gate
(`valueToIndex[v] == 0`, i.e. `v ∉ keys s`) upgrades it to the STRICT window
`Evolution` requires — a nonzero `nextKey` resolves to an actual leaf
(`NextClosed`), so `v = nextKey` would put `v` in the key set. -/
theorem window_strict_of_not_mem
    {s : Finset AbsLeaf} {W : AbsLeaf} {v : UInt256}
    (hclosed : NextClosed s) (hW : W ∈ s)
    (hnot : v ∉ keys s)
    (hwin : W.nextKey = 0 ∨ v ≤ W.nextKey) :
    W.nextKey = 0 ∨ v < W.nextKey := by
  rcases hwin with h0 | hle
  · exact Or.inl h0
  · by_cases h0 : W.nextKey = 0
    · exact Or.inl h0
    · refine Or.inr ?_
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact hlt
      · exfalso
        apply hnot
        obtain ⟨L, hL, hLkey⟩ := hclosed W hW h0
        rw [heq]
        exact Finset.mem_image.mpr ⟨L, hL, hLkey⟩

/-- **THE CONCRETE GUARD IMPLEMENTS ONE SOUND INSERT STEP.**  From a sound
state, the contract's actual loop-exit — the WEAK window `nextKey = 0 ∨
v ≤ nextKey` — together with the dedup gate (`v ∉ keys`) performs a genuine
sound `imtInsert` that adds *exactly* `v`.  Strictness of the window (which
`Evolution`/`imtInsert_*` require) is recovered from the gate via
`window_strict_of_not_mem`, and every invariant of `SoundState` is preserved.
This is the bridge from the concrete insert path to an `Evolution` step:
its two conclusions discharge the `hwin`/soundness premise and the exact
key-set effect an `Evolution` witness must supply. -/
theorem guarded_insert_sound_step
    {s : Finset AbsLeaf} {W : AbsLeaf} {v : UInt256}
    (hs : SoundState s) (hW : W ∈ s)
    (hlow : W.key < v) (hwin : W.nextKey = 0 ∨ v ≤ W.nextKey)
    (hnot : v ∉ keys s) :
    SoundState (imtInsert s W v) ∧ keys (imtInsert s W v) = insert v (keys s) := by
  obtain ⟨hgs, hinj, hnc, hwp⟩ := hs
  have hstrict : W.nextKey = 0 ∨ v < W.nextKey :=
    window_strict_of_not_mem hnc hW hnot hwin
  exact ⟨⟨imtInsert_gapSound hgs hinj hW hlow hstrict,
          imtInsert_keyInj hgs hinj hW hlow hstrict,
          imtInsert_nextClosed hnc hW hlow hstrict,
          imtInsert_windowPos hwp hlow hstrict⟩,
        imtInsert_keys_eq hW⟩

/-- **THE GUARDED INSERT TOGGLES RECLAIMABILITY ATOMICALLY.**  At the exact
delivery event, `v` flips from reclaimable to permanently un-reclaimable:
*before* the guarded insert the low leaf `W` is itself a straddling reclaim
witness for the absent `v`; *after* it, `v` is a key of the tree, so — by
`present_not_reclaimable` on the (still sound) result — NO leaf carries a
window straddling `v`.  A leg cannot be both refunded and delivered across
the single step that delivers it: the no-double-spend guarantee localized to
the delivery boundary. -/
theorem guarded_insert_toggles_reclaimable
    {s : Finset AbsLeaf} {W : AbsLeaf} {v : UInt256}
    (hs : SoundState s) (hW : W ∈ s)
    (hlow : W.key < v) (hwin : W.nextKey = 0 ∨ v ≤ W.nextKey)
    (hnot : v ∉ keys s) :
    (∃ W' ∈ s, W'.key < v ∧ (W'.nextKey = 0 ∨ v < W'.nextKey))
      ∧ ¬ ∃ W' ∈ imtInsert s W v, W'.key < v ∧ (W'.nextKey = 0 ∨ v < W'.nextKey) := by
  have hstrict := window_strict_of_not_mem hs.2.2.1 hW hnot hwin
  refine ⟨⟨W, hW, hlow, hstrict⟩, ?_⟩
  have hstep := guarded_insert_sound_step hs hW hlow hwin hnot
  exact present_not_reclaimable hstep.1.1 (imtInsert_key_mem hW)

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

/-- A guarded history from a sound genesis stays sound at every step. -/
theorem guardedEvolution_sound
    {S : ℕ → Finset AbsLeaf} (hge : GuardedEvolution S) (h0 : SoundState (S 0)) :
    ∀ n, SoundState (S n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    rcases hge n with heq | ⟨W, v, hW, hlow, hwin, hnot, heq⟩
    · rw [heq]; exact ih
    · rw [heq]; exact (guarded_insert_sound_step ih hW hlow hwin hnot).1

/-- **THE CONCRETE GUARD REFINES TO `Evolution`.**  A `GuardedEvolution` from
a sound genesis is an `Evolution`: at each insert step the dedup gate upgrades
the weak window to the strict one (`window_strict_of_not_mem`, discharged
against the step's own sound state).  Bridges every analytic security theorem
to real contract histories. -/
theorem guardedEvolution_isEvolution
    {S : ℕ → Finset AbsLeaf} (hge : GuardedEvolution S) (h0 : SoundState (S 0)) :
    Evolution S := by
  intro n
  rcases hge n with heq | ⟨W, v, hW, hlow, hwin, hnot, heq⟩
  · exact Or.inl heq
  · exact Or.inr ⟨W, v, hW, hlow,
      window_strict_of_not_mem (guardedEvolution_sound hge h0 n).2.2.1 hW hnot hwin, heq⟩

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
theorem guardedEvolution_reclaimable_iff_absent
    {S : ℕ → Finset AbsLeaf} (hge : GuardedEvolution S)
    (hgen : S 0 = ({⟨0, 0⟩} : Finset AbsLeaf))
    {j : ℕ} {v : UInt256} (hv0 : v ≠ 0) :
    (∃ W ∈ S j, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))
      ↔ v ∉ keys (S j) := by
  have h0 : SoundState (S 0) := by rw [hgen]; exact genesis_soundState
  have hzero : (0 : UInt256) ∈ keys (S 0) := by rw [hgen]; exact genesis_zero_mem
  exact reclaimable_iff_absent (guardedEvolution_isEvolution hge h0) h0 hzero hv0

/-- **DELIVERY IS FINAL FOR REAL HISTORIES.**  On-time delivery evidence for
`v` at snapshot `i` (of a guarded history from genesis, with monotone settlement
timestamps) persists at every later snapshot AND forecloses every future reclaim
witness for `v`: a delivered leg can never be raced by a refund. -/
theorem guardedEvolution_delivered_available_forever
    {S : ℕ → Finset AbsLeaf} {t : ℕ → UInt256} {D v : UInt256}
    (hge : GuardedEvolution S) (hgen : S 0 = ({⟨0, 0⟩} : Finset AbsLeaf))
    (htmono : Monotone t)
    {i : ℕ} (hti : t i ≤ D) (hdel : v ∈ keys (S i)) :
    (∀ j, i ≤ j → v ∈ keys (S j))
    ∧ (∀ j (W : AbsLeaf), D < t (j+1) → W ∈ S j → W.key < v →
        ¬ (W.nextKey = 0 ∨ v < W.nextKey)) := by
  have h0 : SoundState (S 0) := by rw [hgen]; exact genesis_soundState
  exact delivered_leg_available_forever (guardedEvolution_isEvolution hge h0)
    h0.1 h0.2.1 htmono hti hdel

/-- **DELIVERY IS EXACTLY-ONCE FOR REAL HISTORIES.**  Along any guarded history
from genesis, a nonzero commit value present at step `n` has EXACTLY ONE entry
step — provenance is a total function on delivered values, so no leg is ever
delivered twice.  The third headline guarantee, hypothesized on only the guard
shape + genesis. -/
theorem guardedEvolution_delivery_exactly_once
    {S : ℕ → Finset AbsLeaf} (hge : GuardedEvolution S)
    (hgen : S 0 = ({⟨0, 0⟩} : Finset AbsLeaf))
    {v : UInt256} (hv0 : v ≠ 0) {n : ℕ} (hmem : v ∈ keys (S n)) :
    ∃! m, m < n ∧ v ∉ keys (S m) ∧ keys (S (m+1)) = insert v (keys (S m)) := by
  have h0s : SoundState (S 0) := by rw [hgen]; exact genesis_soundState
  have hv0' : v ∉ keys (S 0) := by
    rw [hgen]
    intro hmem0
    obtain ⟨L, hL, hLkey⟩ := Finset.mem_image.mp hmem0
    rw [Finset.mem_singleton] at hL
    rw [hL] at hLkey
    exact hv0 hLkey.symm
  exact evolution_key_origin_exists_unique
    (guardedEvolution_isEvolution hge h0s) hv0' hmem

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
theorem forged_padding_witness_breaks_exclusivity {a : UInt256} (ha : a ≠ 0) :
    ∃ (s : Finset AbsLeaf) (v : UInt256) (W : AbsLeaf),
      SoundState s ∧ v ∈ keys s ∧ W ∉ s
        ∧ W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey) := by
  have hapos : (0 : UInt256) < a := Fin.pos_of_ne_zero ha
  have hnlt : ¬ (a < (0 : UInt256)) := by
    intro h; exact absurd (lt_trans hapos h) (lt_irrefl _)
  refine ⟨{⟨0, a⟩, ⟨a, 0⟩}, a, ⟨0, 0⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, hapos, Or.inl rfl⟩
  · -- GapSound
    intro W hW L hL hlt
    simp only [Finset.mem_insert, Finset.mem_singleton] at hW hL
    rcases hW with rfl | rfl <;> rcases hL with rfl | rfl <;>
      simp_all
  · -- KeyInj
    intro A hA B hB hkey
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl <;> simp_all
  · -- NextClosed
    intro W hW hnz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hW
    rcases hW with rfl | rfl
    · exact ⟨⟨a, 0⟩, by simp, rfl⟩
    · exact absurd rfl hnz
  · -- WindowPos
    intro W hW
    simp only [Finset.mem_insert, Finset.mem_singleton] at hW
    rcases hW with rfl | rfl
    · exact Or.inr hapos
    · exact Or.inl rfl
  · -- a is delivered
    exact Finset.mem_image.mpr ⟨⟨a, 0⟩, by simp, rfl⟩
  · -- the forged witness is NOT a leaf
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    constructor
    · intro h; exact ha (congrArg AbsLeaf.nextKey h).symm
    · intro h; exact ha (congrArg AbsLeaf.key h).symm

end IMTAbstract
