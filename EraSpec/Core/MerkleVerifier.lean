import EraSpec.Core.Merkle

/-!
# The verifier's walk at EVERY index and EVERY path length

`EraSpec.Core.MerkleProofSound` proves that an accepted Merkle path pins the leaf
it opens — for an index inside the occupied range, and for a path exactly as long
as the tree is high.  The on-chain verifier (`Merkle.calculateRootMemory`) checks
neither of those things: it accepts any index below `2^pathLength` and any path
length below 256, because it is a pure function of a 32-byte root and has no way
to know how many leaves the tree holds or how high it is.  So the two hypotheses
that file carries are exactly the two degrees of freedom an attacker keeps, and
a soundness statement that assumes them says nothing about the verifier as
deployed.

This file removes both.

## Padded indices

`FullMerkle` fills the positions between `_leafNumber` and `2^_height` with the
zero cascade: the level-0 slot reads `_zeros[0]`, the level-`l` node above only
empty slots reads `_zeros[l]`.  `levelUp_getD_all` is the observation that makes
this uniform: when the `getD` default is the level's own zero, the parent-child
equation `node[l+1][m] = h node[l][2m] node[l][2m+1]` holds at EVERY index, not
just the occupied ones.  With that, the pinning induction needs no range
hypothesis (`walk_pins`), and the root form (`accept_pins_entry`) says an
accepted walk at index `j < 2^k` pins `L.getD j z0` — the real leaf hash if
`j` is occupied, the padding constant `z0` if it is not.

That second case is not a technicality.  `padded_slot_verifies` shows the
honest sibling stream for an EMPTY slot is accepted by the verifier with the
padding constant as its "leaf hash".  Whether that is an attack depends on
whether `z0` collides with a leaf hash — which is precisely what
`EraSpec.Contracts.TreeRoot` settles for the indexed Merkle tree.

## Wrong path lengths

A path shorter than the tree's height, if accepted, presents an INTERIOR node as
the leaf: `accept_forces_height`'s first case re-anchors the walk at level
`height - k` and finds the claimed leaf hash is `h _ _`.  A path longer than the
height, if accepted, must pass through a level-0 entry with a nontrivial walk
still below it: `walkPure_add` splits the walk, and the level-0 entry — a leaf
hash or the padding constant — is again forced to be `h _ _`.  So under the
domain-separation hypotheses "no leaf hash is a node hash" and "the padding
constant is not a node hash" (both true of `keccak` on 96-byte leaf encodings
versus 64-byte node pairs, which is what the `hashLeaf` source comment about
64-byte preimages is protecting), the accepted path length IS the tree height.

Everything here is pure list arithmetic over `MerkleSpec`; node-hash
pair-injectivity is a hypothesis where used, as throughout the corpus.
-/

namespace MerkleSpec.Verifier

open Clear MerkleSpec

/-! ## `getD` toolkit (the `MerkleSpec` copies are private) -/

theorem getD_nil (n : ℕ) (d : UInt256) : ([] : List UInt256).getD n d = d := rfl

theorem getD_cons_succ (a : UInt256) (t : List UInt256) (n : ℕ) (d : UInt256) :
    (a :: t).getD (n + 1) d = t.getD n d := rfl

/-- Out-of-range `getD` is the default. -/
theorem getD_default : ∀ (L : List UInt256) (n : ℕ) (d : UInt256),
    L.length ≤ n → L.getD n d = d
  | [], _, _, _ => rfl
  | _ :: _, 0, _, hn => absurd hn (by simp)
  | _ :: t, n + 1, d, hn =>
    getD_default t n d (by simp only [List.length_cons] at hn; omega)

/-- In-range `getD` is a member. -/
theorem getD_mem : ∀ (L : List UInt256) (n : ℕ) (d : UInt256),
    n < L.length → L.getD n d ∈ L
  | [], _, _, hn => absurd hn (by simp)
  | a :: t, 0, _, _ => List.mem_cons_self a t
  | _ :: t, n + 1, d, hn =>
    List.mem_cons_of_mem _ (getD_mem t n d (by simp only [List.length_cons] at hn; omega))

theorem getD_zero_headD : ∀ (L : List UInt256) (d : UInt256), L.getD 0 d = L.headD d
  | [], _ => rfl
  | _ :: _, _ => rfl

private lemma div_div_pow (j k : ℕ) : j / 2 / 2 ^ k = j / 2 ^ (k + 1) := by
  rw [Nat.div_div_eq_div_mul, ← pow_succ']

/-! ## Every level entry is `h` of the two below it — no range condition -/

/-- **`levelUp_getD` WITHOUT ITS RANGE HYPOTHESIS.**  When the default is the
parent-level zero `h z z`, the parent-child equation holds at every index: in
range it is the pairing, at the frontier the lone left child pairs with `z`,
and beyond the frontier both sides read the zero cascade. -/
theorem levelUp_getD_all (h : Hash) (z : UInt256) :
    ∀ (L : List UInt256) (m : ℕ),
      (levelUp h z L).getD m (h z z) = h (L.getD (2 * m) z) (L.getD (2 * m + 1) z)
  | [], _ => by simp only [levelUp_nil, getD_nil]
  | [a], 0 => rfl
  | [a], m + 1 => by
      have e : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
      rw [levelUp_single, getD_cons_succ, getD_nil, e, getD_cons_succ, getD_nil,
          getD_cons_succ, getD_nil]
  | a :: b :: rest, 0 => rfl
  | a :: b :: rest, m + 1 => by
      have e : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
      rw [e, levelUp_cons₂, getD_cons_succ, getD_cons_succ, getD_cons_succ,
          getD_cons_succ, getD_cons_succ]
      exact levelUp_getD_all h z rest m

/-- The `levels` form: every level-`(l+1)` entry — occupied or padded — is `h`
of the two level-`l` entries below it, all read with the zero cascade as the
default. -/
theorem levels_succ_getD (h : Hash) (z0 : UInt256) (L : List UInt256) (l m : ℕ) :
    (levels h z0 L (l + 1)).getD m (zeros h z0 (l + 1))
      = h ((levels h z0 L l).getD (2 * m) (zeros h z0 l))
          ((levels h z0 L l).getD (2 * m + 1) (zeros h z0 l)) := by
  rw [levels_succ, zeros_succ]
  exact levelUp_getD_all h (zeros h z0 l) _ m

/-- Every entry above level 0 is a node hash. -/
theorem levels_succ_is_node (h : Hash) (z0 : UInt256) (L : List UInt256) (l m : ℕ) :
    ∃ a b : UInt256, (levels h z0 L (l + 1)).getD m (zeros h z0 (l + 1)) = h a b :=
  ⟨_, _, levels_succ_getD h z0 L l m⟩

/-! ## The honest walk, at every index -/

/-- **`walkPure_levels` WITHOUT ITS RANGE HYPOTHESIS.**  A walk from any level
entry — occupied or padded — with the tree's own siblings lands on the node
above it. -/
theorem walkPure_levels_all (h : Hash) (z0 : UInt256) (sibs : ℕ → UInt256)
    (L : List UInt256) :
    ∀ k lvl j : ℕ,
      (∀ l, lvl ≤ l → l < lvl + k →
        sibs l = (levels h z0 L l).getD (sibIdx (j / 2 ^ (l - lvl))) (zeros h z0 l)) →
      walkPure h sibs lvl k j ((levels h z0 L lvl).getD j (zeros h z0 lvl))
        = (levels h z0 L (lvl + k)).getD (j / 2 ^ k) (zeros h z0 (lvl + k)) := by
  intro k
  induction k with
  | zero =>
    intro lvl j _
    simp
  | succ k ih =>
    intro lvl j hsibs
    have hs : sibs lvl = (levels h z0 L lvl).getD (sibIdx j) (zeros h z0 lvl) := by
      have := hsibs lvl (le_refl _) (by omega)
      simpa using this
    have hup := levels_succ_getD h z0 L lvl (j / 2)
    have hacc : (if j % 2 = 1
          then h (sibs lvl) ((levels h z0 L lvl).getD j (zeros h z0 lvl))
          else h ((levels h z0 L lvl).getD j (zeros h z0 lvl)) (sibs lvl))
        = (levels h z0 L (lvl + 1)).getD (j / 2) (zeros h z0 (lvl + 1)) := by
      by_cases hpar : j % 2 = 1
      · rw [show 2 * (j / 2) = j - 1 from by omega,
            show j - 1 + 1 = j from by omega] at hup
        rw [if_pos hpar, hs, hup, show sibIdx j = j - 1 from by simp [sibIdx, hpar]]
      · rw [show 2 * (j / 2) = j from by omega] at hup
        rw [if_neg hpar, hs, hup, show sibIdx j = j + 1 from by simp [sibIdx, hpar]]
    rw [walkPure_succ, hacc]
    have hsibs' : ∀ l, lvl + 1 ≤ l → l < (lvl + 1) + k →
        sibs l = (levels h z0 L l).getD (sibIdx (j / 2 / 2 ^ (l - (lvl + 1))))
          (zeros h z0 l) := by
      intro l hl1 hl2
      have hidx : j / 2 / 2 ^ (l - (lvl + 1)) = j / 2 ^ (l - lvl) := by
        rw [Nat.div_div_eq_div_mul,
            show 2 * 2 ^ (l - (lvl + 1)) = 2 ^ (l - lvl) from by
              rw [show l - lvl = (l - (lvl + 1)) + 1 from by omega]; ring]
      rw [hidx]
      exact hsibs l (by omega) (by omega)
    rw [ih (lvl + 1) (j / 2) hsibs',
        show lvl + 1 + k = lvl + (k + 1) from by omega,
        show j / 2 / 2 ^ k = j / 2 ^ (k + 1) from by
          rw [Nat.div_div_eq_div_mul, show 2 * 2 ^ k = (2 : ℕ) ^ (k + 1) from by ring]]

/-- The sibling stream `FullMerkle.merklePath(j)` returns: at each level the
entry next to the path, or that level's zero at the frontier. -/
def honestSibs (h : Hash) (z0 : UInt256) (L : List UInt256) (j : ℕ) : ℕ → UInt256 :=
  fun l => (levels h z0 L l).getD (sibIdx (j / 2 ^ l)) (zeros h z0 l)

/-- **THE HONEST WALK RECOMPUTES THE ROOT, AT EVERY INDEX BELOW CAPACITY.**  For
an occupied index the accumulator is the leaf hash; for a padded one it is the
padding constant `z0` — and the verifier accepts both. -/
theorem honest_walk_root (h : Hash) (z0 : UInt256) (L : List UInt256) (height j : ℕ)
    (hj : j < 2 ^ height) :
    walkPure h (honestSibs h z0 L j) 0 height j (L.getD j z0) = rootOf h z0 L height := by
  have hmain := walkPure_levels_all h z0 (honestSibs h z0 L j) L height 0 j
    (fun l _ _ => by simp [honestSibs])
  rw [levels_zero, zeros_zero, Nat.zero_add, Nat.div_eq_of_lt hj, getD_zero_headD,
      ← rootOf_def] at hmain
  exact hmain

/-- **A PADDED SLOT VERIFIES.**  Below capacity but beyond the occupied range,
the honest siblings authenticate the padding constant as a leaf.  This is the
verifier working as designed — it cannot tell an empty slot from a full one —
and it is why the padding constant must not be a possible leaf hash. -/
theorem padded_slot_verifies (h : Hash) (z0 : UInt256) (L : List UInt256) (height j : ℕ)
    (hlen : L.length ≤ j) (hj : j < 2 ^ height) :
    walkPure h (honestSibs h z0 L j) 0 height j z0 = rootOf h z0 L height := by
  have := honest_walk_root h z0 L height j hj
  rwa [getD_default L j z0 hlen] at this

/-! ## Soundness: an accepted walk pins the level-0 entry, at every index -/

/-- **`walk_pins_leaf_and_sibs` WITHOUT ITS RANGE HYPOTHESIS.**  A walk that
reaches the tree's node above `j` — any `j` — used the level-`lvl` entry at `j`
as its accumulator (the padding zero, if `j` is empty) and the tree's own
siblings at every level climbed. -/
theorem walk_pins (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L : List UInt256) (sibs : ℕ → UInt256) :
    ∀ (k lvl j : ℕ) (x : UInt256),
      walkPure h sibs lvl k j x
        = (levels h z0 L (lvl + k)).getD (j / 2 ^ k) (zeros h z0 (lvl + k)) →
      (levels h z0 L lvl).getD j (zeros h z0 lvl) = x
        ∧ ∀ l, lvl ≤ l → l < lvl + k →
            sibs l = (levels h z0 L l).getD (sibIdx (j / 2 ^ (l - lvl))) (zeros h z0 l) := by
  intro k
  induction k with
  | zero =>
    intro lvl j x hw
    refine ⟨?_, fun l _ h2 => absurd h2 (by omega)⟩
    rw [walkPure_zero] at hw
    simpa using hw.symm
  | succ k ih =>
    intro lvl j x hw
    have harg : walkPure h sibs (lvl + 1) k (j / 2)
        (if j % 2 = 1 then h (sibs lvl) x else h x (sibs lvl))
        = (levels h z0 L ((lvl + 1) + k)).getD (j / 2 / 2 ^ k)
            (zeros h z0 ((lvl + 1) + k)) := by
      rw [walkPure_succ] at hw
      rw [show (lvl + 1) + k = lvl + (k + 1) from by omega, div_div_pow]
      exact hw
    obtain ⟨hIH, hsIH⟩ := ih (lvl + 1) (j / 2) _ harg
    rw [levels_succ_getD] at hIH
    have habove : ∀ l, lvl + 1 ≤ l → l < lvl + (k + 1) →
        sibs l = (levels h z0 L l).getD (sibIdx (j / 2 ^ (l - lvl))) (zeros h z0 l) := by
      intro l h1 h2
      have := hsIH l h1 (by omega)
      rw [show l - (lvl + 1) = (l - lvl) - 1 from by omega] at this
      rw [show j / 2 / 2 ^ (l - lvl - 1) = j / 2 ^ ((l - lvl - 1) + 1) from div_div_pow _ _,
          show (l - lvl - 1) + 1 = l - lvl from by omega] at this
      exact this
    by_cases hpar : j % 2 = 1
    · rw [if_pos hpar] at hIH
      rw [show 2 * (j / 2) = j - 1 from by omega,
          show j - 1 + 1 = j from by omega] at hIH
      obtain ⟨hs, hx⟩ := hinj _ _ _ _ hIH.symm
      refine ⟨hx.symm, ?_⟩
      intro l h1 h2
      rcases Nat.eq_or_lt_of_le h1 with heq | h1'
      · rw [← heq, show lvl - lvl = 0 from by omega, pow_zero, Nat.div_one,
            show sibIdx j = j - 1 from by simp [sibIdx, hpar]]
        exact hs
      · exact habove l (by omega) h2
    · rw [if_neg hpar] at hIH
      rw [show 2 * (j / 2) = j from by omega] at hIH
      obtain ⟨hx, hs⟩ := hinj _ _ _ _ hIH.symm
      refine ⟨hx.symm, ?_⟩
      intro l h1 h2
      rcases Nat.eq_or_lt_of_le h1 with heq | h1'
      · rw [← heq, show lvl - lvl = 0 from by omega, pow_zero, Nat.div_one,
            show sibIdx j = j + 1 from by simp [sibIdx, hpar]]
        exact hs
      · exact habove l (by omega) h2

/-- **ROOT FORM.**  An accepted walk of length `k` from any index `j < 2^k`
against the root at height `k` pins the level-0 entry at `j`, padding included:
`L.getD j z0` is the leaf hash if `j` is occupied and `z0` otherwise.  Note that
no capacity hypothesis is needed for soundness — a tree wider than `2^k` simply
has leaves its root does not authenticate. -/
theorem accept_pins_entry (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L : List UInt256) (sibs : ℕ → UInt256) (k j : ℕ) (x : UInt256)
    (hj : j < 2 ^ k)
    (haccept : walkPure h sibs 0 k j x = rootOf h z0 L k) :
    L.getD j z0 = x := by
  have hroot : (levels h z0 L (0 + k)).getD (j / 2 ^ k) (zeros h z0 (0 + k))
      = rootOf h z0 L k := by
    rw [Nat.zero_add, Nat.div_eq_of_lt hj, rootOf_def, getD_zero_headD]
  have := (walk_pins h z0 hinj L sibs k 0 j x (by rw [hroot]; exact haccept)).1
  simpa using this

/-- The two cases of `accept_pins_entry`, spelled out: either the index is
occupied and the walk's leaf IS that entry, or it is padding and the walk's
leaf IS the padding constant. -/
theorem accept_pins_entry_cases (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L : List UInt256) (sibs : ℕ → UInt256) (k j : ℕ) (x : UInt256)
    (hj : j < 2 ^ k)
    (haccept : walkPure h sibs 0 k j x = rootOf h z0 L k) :
    (j < L.length ∧ L.getD j z0 = x) ∨ (L.length ≤ j ∧ x = z0) := by
  have hx := accept_pins_entry h z0 hinj L sibs k j x hj haccept
  by_cases hjL : j < L.length
  · exact Or.inl ⟨hjL, hx⟩
  · refine Or.inr ⟨by omega, ?_⟩
    rw [← hx]
    exact getD_default L j z0 (by omega)

/-! ## Wrong path lengths -/

/-- A walk splits at any level: the first `k₁` steps, then `k₂` more from the
node they reach. -/
theorem walkPure_add (h : Hash) (sibs : ℕ → UInt256) :
    ∀ (k₁ k₂ lvl idx : ℕ) (x : UInt256),
      walkPure h sibs lvl (k₁ + k₂) idx x
        = walkPure h sibs (lvl + k₁) k₂ (idx / 2 ^ k₁) (walkPure h sibs lvl k₁ idx x)
  | 0, k₂, lvl, idx, x => by simp
  | k₁ + 1, k₂, lvl, idx, x => by
      rw [show k₁ + 1 + k₂ = (k₁ + k₂) + 1 from by omega, walkPure_succ,
          walkPure_add h sibs k₁ k₂ (lvl + 1) (idx / 2) _,
          show lvl + 1 + k₁ = lvl + (k₁ + 1) from by omega, div_div_pow,
          walkPure_succ]

/-- The starting level only decides which sibling entries are read: a walk from
level `lvl + d` is a walk from level `lvl` over the shifted stream. -/
theorem walkPure_shift (h : Hash) (sibs : ℕ → UInt256) (d : ℕ) :
    ∀ (k lvl idx : ℕ) (x : UInt256),
      walkPure h sibs (lvl + d) k idx x = walkPure h (fun l => sibs (l + d)) lvl k idx x
  | 0, _, _, _ => by rw [walkPure_zero, walkPure_zero]
  | k + 1, lvl, idx, x => by
      rw [walkPure_succ, walkPure_succ, show lvl + d + 1 = (lvl + 1) + d from by omega]
      exact walkPure_shift h sibs d k (lvl + 1) (idx / 2) _

/-- Any walk of positive length ends in a node hash. -/
theorem walkPure_succ_is_node (h : Hash) (sibs : ℕ → UInt256) :
    ∀ (k lvl idx : ℕ) (x : UInt256), ∃ a b : UInt256, walkPure h sibs lvl (k + 1) idx x = h a b
  | 0, lvl, idx, x => by
      rw [walkPure_succ, walkPure_zero]
      by_cases hpar : idx % 2 = 1
      · exact ⟨_, _, if_pos hpar⟩
      · exact ⟨_, _, if_neg hpar⟩
  | k + 1, lvl, idx, x => by
      rw [walkPure_succ]
      exact walkPure_succ_is_node h sibs k (lvl + 1) (idx / 2) _

/-- **THE ACCEPTED PATH LENGTH IS THE TREE HEIGHT.**  Under domain separation —
no level-0 entry (leaf hash or padding constant) is a node hash, and neither is
the claimed leaf hash `x` — a walk accepted against the root at `height` has
length exactly `height`.

Shorter: re-anchor the walk at level `height - k`; it then pins `x` to an
entry of a level above 0, which is a node hash.  Longer: split off the excess
below; the level-0 entry it must reach is then a node hash. -/
theorem accept_forces_height (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L : List UInt256) (hL : ∀ y ∈ L, ∀ a b : UInt256, y ≠ h a b)
    (hz0 : ∀ a b : UInt256, z0 ≠ h a b)
    (sibs : ℕ → UInt256) (k height j : ℕ) (x : UInt256) (hx : ∀ a b : UInt256, x ≠ h a b)
    (hj : j < 2 ^ k)
    (haccept : walkPure h sibs 0 k j x = rootOf h z0 L height) : k = height := by
  rcases lt_trichotomy k height with hlt | heq | hgt
  · -- too short: the claimed leaf is an interior node
    exfalso
    obtain ⟨d, hd⟩ : ∃ d, height = (d + 1) + k := ⟨height - k - 1, by omega⟩
    have hshift : walkPure h (fun l => sibs (l - (d + 1))) (0 + (d + 1)) k j x
        = walkPure h sibs 0 k j x := by
      rw [walkPure_shift]
      exact walkPure_congr_sibs h _ sibs k 0 j x (fun l _ _ => by simp)
    have hw : walkPure h (fun l => sibs (l - (d + 1))) (d + 1) k j x
        = (levels h z0 L ((d + 1) + k)).getD (j / 2 ^ k) (zeros h z0 ((d + 1) + k)) := by
      rw [Nat.zero_add] at hshift
      rw [hshift, haccept, hd, Nat.div_eq_of_lt hj, rootOf_def, getD_zero_headD]
    obtain ⟨a, b, hab⟩ := levels_succ_is_node h z0 L d j
    exact hx a b ((walk_pins h z0 hinj L _ k (d + 1) j x hw).1.symm.trans hab)
  · exact heq
  · -- too long: the level-0 entry the walk passes through is a node hash
    exfalso
    obtain ⟨m, hm⟩ : ∃ m, k = (m + 1) + height := ⟨k - height - 1, by omega⟩
    have hsplit := walkPure_add h sibs (m + 1) height 0 j x
    rw [← hm, haccept, walkPure_shift] at hsplit
    have hj' : j / 2 ^ (m + 1) < 2 ^ height := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      have e : height + (m + 1) = k := by omega
      rw [e]
      exact hj
    obtain ⟨a, b, hab⟩ := walkPure_succ_is_node h sibs m 0 j x
    rcases accept_pins_entry_cases h z0 hinj L _ height (j / 2 ^ (m + 1)) _ hj' hsplit.symm
      with ⟨hlt, hget⟩ | ⟨_, hpad⟩
    · exact hL _ (getD_mem L _ z0 hlt) a b (hget.trans hab)
    · exact hz0 a b (hpad.symm.trans hab)

/-- **FULL SOUNDNESS OF THE DEPLOYED VERIFIER.**  For any index and any path
length the verifier accepts, under pair-injectivity and domain separation: the
length is the tree's height and the claimed leaf hash is the level-0 entry at
that index — a real leaf hash if the index is occupied, the padding constant if
not. -/
theorem accept_pins_entry_any_length (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L : List UInt256) (hL : ∀ y ∈ L, ∀ a b : UInt256, y ≠ h a b)
    (hz0 : ∀ a b : UInt256, z0 ≠ h a b)
    (sibs : ℕ → UInt256) (k height j : ℕ) (x : UInt256) (hx : ∀ a b : UInt256, x ≠ h a b)
    (hj : j < 2 ^ k)
    (haccept : walkPure h sibs 0 k j x = rootOf h z0 L height) :
    k = height ∧ L.getD j z0 = x := by
  have hk := accept_forces_height h z0 hinj L hL hz0 sibs k height j x hx hj haccept
  subst hk
  exact ⟨rfl, accept_pins_entry h z0 hinj L sibs k j x hj haccept⟩

end MerkleSpec.Verifier
