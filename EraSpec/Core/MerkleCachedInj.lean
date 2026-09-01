import EraSpec.Core.Merkle

/- EXTRACTED from contracts-formal-verification (`specs/specs/MerkleCachedInj.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  M-D, RESTRICTED TO THE PAIRS THE TREE ACTUALLY HASHES.

  `MerkleSpec.rootOf_inj_of_h_inj` asks for node-hash pair-injectivity at ALL arguments:

      hinj : ∀ a b c d, h a b = h c d → a = c ∧ b = d

  `specs/CachedHashInj.lean` derived pair-injectivity for the deployed hash `hashOf SF`, but only
  ON CACHED PAIRS — necessarily, since an uncached pair hashes to `0` and injectivity fails
  vacuously off the cache.  So M-D could not be instantiated with the contract's own hash: the
  last instance of the over-strength that forced four weakenings in `FoldWalkBridge` and the
  restricted form of `root_binding`.

  This file removes it.  `levelUp` hashes exactly the ADJACENT PAIRS of a level (plus
  `(last, zero)` when the level has odd length), so the pairs M-D's induction touches are
  enumerable: `levelPairs`.  Restricting injectivity to a predicate `P` holding on those pairs is
  then enough, and a "cached in SF" predicate is such a `P` — with a pair count linear in the tree
  size rather than universal.

  The unrestricted theorems are derived from the restricted ones as the `P := True` instances, so
  this is a generalization rather than a parallel development.  Axiom-free.
-/

namespace Clear.MerkleCachedInj

open Clear MerkleSpec

/-- The pairs `levelUp` hashes at one level: adjacent pairs, and `(last, z)` if odd-length. -/
def levelPairs (z : UInt256) : List UInt256 → List (UInt256 × UInt256)
  | [] => []
  | [a] => [(a, z)]
  | a :: b :: rest => (a, b) :: levelPairs z rest

@[simp] theorem levelPairs_nil (z : UInt256) : levelPairs z [] = [] := rfl

@[simp] theorem levelPairs_single (z a : UInt256) : levelPairs z [a] = [(a, z)] := rfl

@[simp] theorem levelPairs_cons₂ (z a b : UInt256) (rest : List UInt256) :
    levelPairs z (a :: b :: rest) = (a, b) :: levelPairs z rest := rfl

/-- Every pair a level's `levelUp` hashes satisfies `P` — the restriction hypothesis, named. -/
def PairsOK (P : UInt256 → UInt256 → Prop) (z : UInt256) (L : List UInt256) : Prop :=
  ∀ p ∈ levelPairs z L, P p.1 p.2

/-- **`levelUp` IS INJECTIVE ON `P`-PAIRS.**  As `MerkleSpec.levelUp_inj`, but the node hash need
only be injective on pairs satisfying `P`, and `P` need only hold on the pairs the two levels
actually contribute. -/
theorem levelUp_inj_on (h : Hash) (z : UInt256) {P : UInt256 → UInt256 → Prop}
    (hinj : ∀ a b c d : UInt256, P a b → P c d → h a b = h c d → a = c ∧ b = d) :
    ∀ L₁ L₂ : List UInt256, L₁.length = L₂.length →
      PairsOK P z L₁ → PairsOK P z L₂ →
      levelUp h z L₁ = levelUp h z L₂ → L₁ = L₂
  | [], [], _, _, _, _ => rfl
  | [], _ :: _ :: _, hlen, _, _, _ => by
      simp only [List.length_nil, List.length_cons] at hlen; try omega
  | [], [_], hlen, _, _, _ => by
      simp only [List.length_nil, List.length_cons] at hlen; try omega
  | [_], [], hlen, _, _, _ => by
      simp only [List.length_nil, List.length_cons] at hlen; try omega
  | _ :: _ :: _, [], hlen, _, _, _ => by
      simp only [List.length_nil, List.length_cons] at hlen; try omega
  | [a], [c], _, hp₁, hp₂, he => by
      rw [levelUp_single, levelUp_single, List.cons.injEq] at he
      have ha : P a z := hp₁ (a, z) (by simp)
      have hc : P c z := hp₂ (c, z) (by simp)
      rw [(hinj a z c z ha hc he.1).1]
  | [_], _ :: _ :: _, hlen, _, _, _ => by
      simp only [List.length_cons, List.length_nil] at hlen; try omega
  | _ :: _ :: _, [_], hlen, _, _, _ => by
      simp only [List.length_cons, List.length_nil] at hlen; try omega
  | a :: b :: rest, c :: d :: rest', hlen, hp₁, hp₂, he => by
      rw [levelUp_cons₂, levelUp_cons₂, List.cons.injEq] at he
      obtain ⟨hh, ht⟩ := he
      have hab : P a b := hp₁ (a, b) (by simp)
      have hcd : P c d := hp₂ (c, d) (by simp)
      obtain ⟨rfl, rfl⟩ := hinj a b c d hab hcd hh
      have hrl : rest.length = rest'.length := by
        simp only [List.length_cons] at hlen; omega
      have hr₁ : PairsOK P z rest := fun p hp => hp₁ p (by simp [hp])
      have hr₂ : PairsOK P z rest' := fun p hp => hp₂ p (by simp [hp])
      rw [levelUp_inj_on h z hinj rest rest' hrl hr₁ hr₂ ht]

/-- **Equal level-`l` lists force equal leaves, on `P`-pairs.**  The restriction is needed at
every level below `l`, for both lists — which is exactly the set of pairs the tree hashes. -/
theorem levels_inj_on (h : Hash) (z0 : UInt256) {P : UInt256 → UInt256 → Prop}
    (hinj : ∀ a b c d : UInt256, P a b → P c d → h a b = h c d → a = c ∧ b = d)
    (L₁ L₂ : List UInt256) (hlen : L₁.length = L₂.length) :
    ∀ l, (∀ l' < l, PairsOK P (zeros h z0 l') (levels h z0 L₁ l')) →
      (∀ l' < l, PairsOK P (zeros h z0 l') (levels h z0 L₂ l')) →
      levels h z0 L₁ l = levels h z0 L₂ l → L₁ = L₂
  | 0 => by intro _ _ he; rw [levels_zero, levels_zero] at he; exact he
  | l + 1 => fun hp₁ hp₂ he => by
      rw [levels_succ, levels_succ] at he
      refine levels_inj_on h z0 hinj L₁ L₂ hlen l
        (fun l' hl' => hp₁ l' (by omega)) (fun l' hl' => hp₂ l' (by omega)) ?_
      exact levelUp_inj_on h (zeros h z0 l) hinj _ _
        (levels_length_eq h z0 L₁ L₂ hlen l)
        (hp₁ l (by omega)) (hp₂ l (by omega)) he

/-- **M-D ON CACHED PAIRS.**  For a non-full tree, the recomputed root pins the whole leaf list —
with node-hash injectivity required only on the pairs the tree's own levels hash.

This is the form the deployed hash can instantiate: `CachedHashInj.hashOf_pair_inj` supplies
`hinj` for `P := "cached in SF"`, and the pair obligation is linear in the tree size. -/
theorem rootOf_inj_on (h : Hash) (z0 : UInt256) {P : UInt256 → UInt256 → Prop}
    (hinj : ∀ a b c d : UInt256, P a b → P c d → h a b = h c d → a = c ∧ b = d)
    (L₁ L₂ : List UInt256) (height : ℕ)
    (hlen : L₁.length = L₂.length) (hne : L₁.length ≠ 0)
    (hcap : L₁.length ≤ 2 ^ height)
    (hp₁ : ∀ l < height, PairsOK P (zeros h z0 l) (levels h z0 L₁ l))
    (hp₂ : ∀ l < height, PairsOK P (zeros h z0 l) (levels h z0 L₂ l))
    (hroot : rootOf h z0 L₁ height = rootOf h z0 L₂ height) :
    L₁ = L₂ := by
  refine levels_inj_on h z0 hinj L₁ L₂ hlen height hp₁ hp₂ ?_
  rw [levels_height_singleton h z0 L₁ height hne hcap,
      levels_height_singleton h z0 L₂ height (hlen ▸ hne) (hlen ▸ hcap),
      hroot]

/-- The unrestricted M-D is the `P := True` instance — recorded so the restriction is visibly a
generalization of `MerkleSpec.rootOf_inj_of_h_inj`, not a parallel result. -/
theorem rootOf_inj_of_h_inj_of_on (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L₁ L₂ : List UInt256) (height : ℕ)
    (hlen : L₁.length = L₂.length) (hne : L₁.length ≠ 0)
    (hcap : L₁.length ≤ 2 ^ height)
    (hroot : rootOf h z0 L₁ height = rootOf h z0 L₂ height) :
    L₁ = L₂ :=
  rootOf_inj_on h z0 (P := fun _ _ => True) (fun a b c d _ _ he => hinj a b c d he)
    L₁ L₂ height hlen hne hcap (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) hroot

/-- **Entry-level corollary, restricted.**  Equal roots force equal entries at every index —
the form `AttackVectors.RootBinding.getD_of_rootOf_eq` supplies to root binding, now on
`P`-restricted injectivity. -/
theorem getD_of_rootOf_eq_on (h : Hash) (z0 : UInt256) {P : UInt256 → UInt256 → Prop}
    (hinj : ∀ a b c d : UInt256, P a b → P c d → h a b = h c d → a = c ∧ b = d)
    (L₁ L₂ : List UInt256) (height : ℕ)
    (hlen : L₁.length = L₂.length) (hne : L₁.length ≠ 0)
    (hcap : L₁.length ≤ 2 ^ height)
    (hp₁ : ∀ l < height, PairsOK P (zeros h z0 l) (levels h z0 L₁ l))
    (hp₂ : ∀ l < height, PairsOK P (zeros h z0 l) (levels h z0 L₂ l))
    (hroot : rootOf h z0 L₁ height = rootOf h z0 L₂ height)
    (i : ℕ) (dflt : UInt256) : L₁.getD i dflt = L₂.getD i dflt := by
  rw [rootOf_inj_on h z0 hinj L₁ L₂ height hlen hne hcap hp₁ hp₂ hroot]

end Clear.MerkleCachedInj
