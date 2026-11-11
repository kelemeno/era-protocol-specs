import EraSpec.Contracts.L2InteropCommitmentTree.Properties.CachedRoot
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.RunHeight
import EraSpec.Contracts.FullMerkle.Proofs.CachedNodes

/-!
# Proofs: the stored root is the published root

Proofs of `EraSpec.Contracts.L2InteropCommitmentTree.Properties.CachedRoot`.  The
`FullMerkle` content is `EraSpec.Contracts.FullMerkle.Proofs.CachedNodes` (every call keeps
the storage caching the fold).  What this file adds is that `IndexedMerkleTree`'s two
calls per insert move the cached leaf list exactly as `leafHashes_insert` says, so the
invariant holds along every run.  It also transfers the `RunHeight` headline from the
honest sibling stream to the contract's own `merklePath` output.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract MerkleSpec MerkleSpec.Verifier AttackVectors.CapacityInvariant

/-! ## The calls -/

lemma leafHashes_setup (hl : LeafHash) : leafHashes hl setup = [] ++ [zeroLeafHash hl] := rfl

theorem cSetup_caches (h : Hash) (hl : LeafHash) :
    ∃ S : CState, cSetup h hl = some S ∧ S.tree = setup
      ∧ S.toH = hSetup ∧ FullMerkle.Represents h (zeroLeafHash hl) (leafHashes hl S.tree) S.fm := by
  have hR₀ := (FullMerkle.setup_represents_empty h (zeroLeafHash hl)).1
  obtain ⟨F, hp, hR, hd⟩ :=
    FullMerkle.pushNewLeaf_computes_root h (zeroLeafHash hl) [] _ (zeroLeafHash hl) hR₀
  refine ⟨⟨setup, F⟩, ?_, rfl, ?_, ?_⟩
  · simp [cSetup, hp]
  · show (⟨setup, ⟨F.leafNumber, F.height⟩⟩ : HState) = ⟨setup, setupDims⟩
    rw [hd]
    rfl
  · rw [leafHashes_setup]
    exact hR

theorem cInsert_caches (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : CState) (v : UInt256)
    (low : ℕ) (hR : FullMerkle.Represents h z0 (leafHashes hl S.tree) S.fm)
    (hlow : low < S.tree.leafCount) :
    ∃ (S' : CState) (r : UInt256), cInsert h hl S v low = some (S', r)
      ∧ S'.tree = insert S.tree v low ∧ S'.toH = hInsert S.toH v low
      ∧ FullMerkle.Represents h z0 (leafHashes hl S'.tree) S'.fm
      ∧ r = root h z0 hl S'.tree S'.fm.height := by
  obtain ⟨F₁, hu, hR₁, hH₁, hN₁⟩ := FullMerkle.updateLeaf_computes_root h z0 _ S.fm low
    (hl { S.tree.leaf low with nextIndex := S.tree.leafCount, nextValue := v }) hR
    (by rwa [leafHashes_length])
  obtain ⟨F₂, hp, hR₂, hd₂⟩ := FullMerkle.pushNewLeaf_computes_root h z0 _ F₁
    (hl ⟨v, (S.tree.leaf low).nextIndex, (S.tree.leaf low).nextValue⟩) hR₁
  refine ⟨⟨insert S.tree v low, F₂⟩, rootOf h z0
      ((leafHashes hl S.tree).set low
          (hl { S.tree.leaf low with nextIndex := S.tree.leafCount, nextValue := v })
        ++ [hl ⟨v, (S.tree.leaf low).nextIndex, (S.tree.leaf low).nextValue⟩]) F₂.height,
    ?_, rfl, ?_, ?_, ?_⟩
  · simp only [cInsert, hu, hp, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  · show (⟨insert S.tree v low, ⟨F₂.leafNumber, F₂.height⟩⟩ : HState)
      = ⟨insert S.tree v low, push ⟨S.fm.leafNumber, S.fm.height⟩⟩
    rw [hd₂, hH₁, hN₁]
  · show FullMerkle.Represents h z0 (leafHashes hl (insert S.tree v low)) F₂
    rw [leafHashes_insert hlow]
    exact hR₂
  · show rootOf h z0 _ F₂.height = rootOf h z0 (leafHashes hl (insert S.tree v low)) F₂.height
    rw [leafHashes_insert hlow]

/-! ## Along runs -/

private lemma cReaches_caches {h : Hash} {hl : LeafHash} {S : CState} (hS : CReaches h hl S) :
    HReaches hSetup S.toH ∧ FullMerkle.Represents h (zeroLeafHash hl) (leafHashes hl S.tree) S.fm := by
  induction hS with
  | init hs =>
    obtain ⟨S₀, hs₀, _, hH, hR⟩ := cSetup_caches h hl
    rw [hs] at hs₀
    cases hs₀
    exact ⟨hH ▸ HReaches.refl, hR⟩
  | @insert S S' v low r _ hg hins ih =>
    obtain ⟨hH, hR⟩ := ih
    obtain ⟨S'', r'', hins', _, htoH, hR'', _⟩ :=
      cInsert_caches h (zeroLeafHash hl) hl S v low hR hg.inBounds
    rw [hins] at hins'
    obtain ⟨hS', _⟩ := Prod.mk.inj (Option.some.inj hins')
    subst hS'
    exact ⟨htoH ▸ HReaches.tail hH hg, hR''⟩

/-- `root()` of a state whose storage caches its leaf hashes is the published root of its
view. -/
private lemma root_eq_published {h : Hash} {z0 : UInt256} {hl : LeafHash} {S : CState}
    (hR : FullMerkle.Represents h z0 (leafHashes hl S.tree) S.fm) :
    S.root = some (S.toH.root h z0 hl) := by
  rw [CState.root, FullMerkle.root_is_fold h z0 _ S.fm hR]
  rfl

theorem cReaches_root_is_published (h : Hash) (hl : LeafHash) (S : CState)
    (hS : CReaches h hl S) :
    HReaches hSetup S.toH
      ∧ FullMerkle.Represents h (zeroLeafHash hl) (leafHashes hl S.tree) S.fm
      ∧ S.root = some (S.toH.root h (zeroLeafHash hl) hl) :=
  ⟨(cReaches_caches hS).1, (cReaches_caches hS).2, root_eq_published (cReaches_caches hS).2⟩

theorem cRun_reaches {h : Hash} {hl : LeafHash} {R : ℕ → CState} (hR : CRun h hl R)
    (h0 : cSetup h hl = some (R 0)) (n : ℕ) : CReaches h hl (R n) := by
  induction n with
  | zero => exact CReaches.init h0
  | succ n ih =>
    rcases hR n with heq | ⟨v, low, r, hg, hins⟩
    · rw [heq]; exact ih
    · exact CReaches.insert ih hg hins

theorem cRun_root_is_published (h : Hash) (hl : LeafHash) (R : ℕ → CState) (hR : CRun h hl R)
    (h0 : cSetup h hl = some (R 0)) (n : ℕ) :
    CReaches h hl (R n) ∧ HReaches hSetup (R n).toH
      ∧ (R n).root = some ((R n).toH.root h (zeroLeafHash hl) hl) :=
  have hS := cRun_reaches hR h0 n
  ⟨hS, (cReaches_root_is_published h hl _ hS).1, (cReaches_root_is_published h hl _ hS).2.2⟩

theorem cInsert_returns_published_root (h : Hash) (hl : LeafHash) (S : CState) (v : UInt256)
    (low : ℕ) (hS : CReaches h hl S) (hg : InsertGuard S.tree v low) :
    ∃ (S' : CState) (r : UInt256), cInsert h hl S v low = some (S', r) ∧ CReaches h hl S'
      ∧ S'.toH = hInsert S.toH v low ∧ S'.root = some r
      ∧ r = (hInsert S.toH v low).root h (zeroLeafHash hl) hl := by
  obtain ⟨S', r, hins, _, htoH, hR', hr⟩ :=
    cInsert_caches h (zeroLeafHash hl) hl S v low (cReaches_caches hS).2 hg.inBounds
  refine ⟨S', r, hins, CReaches.insert hS hg hins, htoH, ?_, ?_⟩
  · rw [root_eq_published hR', hr]
    rfl
  · rw [← htoH, hr]
    rfl

theorem cInsert_returns_the_walk (h : Hash) (hl : LeafHash) (S S' : CState) (v : UInt256)
    (low : ℕ) (r : UInt256) (hS : CReaches h hl S) (hg : InsertGuard S.tree v low)
    (hins : cInsert h hl S v low = some (S', r)) :
    r = walkPure h
          (honestSibs h (zeroLeafHash hl)
            ((leafHashes hl S.tree).set low
              (hl { S.tree.leaf low with nextIndex := S.tree.leafCount, nextValue := v }))
            S.tree.leafCount)
          0 S'.fm.height S.tree.leafCount
          (hl ⟨v, (S.tree.leaf low).nextIndex, (S.tree.leaf low).nextValue⟩) := by
  obtain ⟨S'', r'', hins', _, htoH, _, hr⟩ := cInsert_returns_published_root h hl S v low hS hg
  rw [hins] at hins'
  obtain ⟨hS', hr'⟩ := Prod.mk.inj (Option.some.inj hins')
  subst hS' hr'
  rw [hr, root_after_insert_own_height h (zeroLeafHash hl) hl S.toH v low
    (cReaches_root_is_published h hl S hS).1 hg, ← htoH]
  rfl

theorem hReaches_lifts (h : Hash) (hl : LeafHash) (S : HState) (hS : HReaches hSetup S) :
    ∃ C : CState, CReaches h hl C ∧ C.toH = S := by
  induction hS with
  | refl =>
    obtain ⟨C, hC, _, hH, _⟩ := cSetup_caches h hl
    exact ⟨C, CReaches.init hC, hH⟩
  | @tail U _ v low hg ih =>
    obtain ⟨C, hC, hCU⟩ := ih
    have hg' : InsertGuard C.tree v low := by
      have : C.tree = U.tree := congrArg HState.tree hCU
      rwa [this]
    obtain ⟨C', r, hins, _, htoH, _, _⟩ :=
      cInsert_caches h (zeroLeafHash hl) hl C v low (cReaches_caches hC).2 hg'.inBounds
    exact ⟨C', CReaches.insert hC hg' hins, by rw [htoH, hCU]⟩

open Classical in
/-- The lift of a `RunHeight` run: idle steps stay, and an insert step replays the insert
the run makes (choice picks its value and low leaf) on the whole storage. -/
private noncomputable def liftRun (h : Hash) (hl : LeafHash) (R : ℕ → HState) (C₀ : CState) :
    ℕ → CState
  | 0 => C₀
  | n + 1 =>
    if hex : ∃ (v : UInt256) (low : ℕ),
        InsertGuard (R n).tree v low ∧ R (n + 1) = hInsert (R n) v low then
      ((cInsert h hl (liftRun h hl R C₀ n) hex.choose hex.choose_spec.choose).map
        Prod.fst).getD (liftRun h hl R C₀ n)
    else liftRun h hl R C₀ n

/-- One step of the lift: from a reached state whose view is `R n`, the next lifted state
is reached, its view is `R (n + 1)`, and the step is a `CRun` step. -/
private lemma liftRun_step {h : Hash} {hl : LeafHash} {R : ℕ → HState} (hR : HRun R)
    (C₀ : CState) (n : ℕ) (hC : CReaches h hl (liftRun h hl R C₀ n))
    (hview : (liftRun h hl R C₀ n).toH = R n) :
    CReaches h hl (liftRun h hl R C₀ (n + 1)) ∧ (liftRun h hl R C₀ (n + 1)).toH = R (n + 1)
      ∧ (liftRun h hl R C₀ (n + 1) = liftRun h hl R C₀ n
        ∨ ∃ (v : UInt256) (low : ℕ) (r : UInt256),
            InsertGuard (liftRun h hl R C₀ n).tree v low
            ∧ cInsert h hl (liftRun h hl R C₀ n) v low = some (liftRun h hl R C₀ (n + 1), r)) := by
  have htree : (liftRun h hl R C₀ n).tree = (R n).tree := congrArg HState.tree hview
  by_cases hex : ∃ (v : UInt256) (low : ℕ),
      InsertGuard (R n).tree v low ∧ R (n + 1) = hInsert (R n) v low
  · obtain ⟨hg, hnext⟩ := hex.choose_spec.choose_spec
    have hg' : InsertGuard (liftRun h hl R C₀ n).tree hex.choose hex.choose_spec.choose := by
      rwa [htree]
    obtain ⟨C', r, hins, _, htoH, _, _⟩ := cInsert_caches h (zeroLeafHash hl) hl _ _ _
      (cReaches_caches hC).2 hg'.inBounds
    have hlift : liftRun h hl R C₀ (n + 1) = C' := by
      rw [liftRun, dite_eq_left hex, hins]
      rfl
    rw [hlift]
    refine ⟨CReaches.insert hC hg' hins, ?_, Or.inr ⟨_, _, r, hg', hins⟩⟩
    rw [htoH, hview]
    exact hnext.symm
  · have hlift : liftRun h hl R C₀ (n + 1) = liftRun h hl R C₀ n := by
      rw [liftRun, dite_eq_right hex]
    have hidle : R (n + 1) = R n := by
      rcases hR n with heq | ⟨v, low, hg, heq⟩
      · exact heq
      · exact absurd ⟨v, low, hg, heq⟩ hex
    rw [hlift, hidle]
    exact ⟨hC, hview, Or.inl rfl⟩

theorem hRun_lifts_to_cRun (h : Hash) (hl : LeafHash) (R : ℕ → HState) (hR : HRun R)
    (h0 : R 0 = hSetup) :
    ∃ C : ℕ → CState, CRun h hl C ∧ cSetup h hl = some (C 0) ∧ ∀ n, (C n).toH = R n := by
  obtain ⟨C₀, hC₀, _, hH₀, _⟩ := cSetup_caches h hl
  have inv : ∀ n, CReaches h hl (liftRun h hl R C₀ n) ∧ (liftRun h hl R C₀ n).toH = R n := by
    intro n
    induction n with
    | zero => exact ⟨CReaches.init hC₀, by rwa [h0]⟩
    | succ n ih =>
      obtain ⟨hC, hview, _⟩ := liftRun_step hR C₀ n ih.1 ih.2
      exact ⟨hC, hview⟩
  refine ⟨liftRun h hl R C₀, fun n => (liftRun_step hR C₀ n (inv n).1 (inv n).2).2.2, hC₀,
    fun n => (inv n).2⟩

/-! ## The headline against the contract's own root and paths -/

/-- The contract's path for leaf `i`: `merklePath(i)` on storage caching `leafHashes`. -/
private lemma contract_path {h : Hash} {z0 : UInt256} {hl : LeafHash} {S : CState}
    (hR : FullMerkle.Represents h z0 (leafHashes hl S.tree) S.fm) {i : ℕ}
    (hi : i < S.tree.leafCount) :
    S.merklePath i
      = some ((List.range S.fm.height).map (honestSibs h z0 (leafHashes hl S.tree) i)) :=
  FullMerkle.merklePath_is_honest h z0 _ S.fm i hR (by rwa [leafHashes_length])

/-- An accepted path at height `H` over the honest stream is accepted over the contract's
returned path, which has length `H`. -/
private lemma pathAccepts_contract {h : Hash} {z0 : UInt256} {L : List UInt256} {R : UInt256}
    {H i : ℕ} {x : UInt256} (hA : PathAccepts h R (honestSibs h z0 L i) H i x) :
    PathAccepts h R (FullMerkle.pathSibs ((List.range H).map (honestSibs h z0 L i)))
      ((List.range H).map (honestSibs h z0 L i)).length i x := by
  rw [List.length_map, List.length_range]
  refine ⟨hA.inBounds, ?_⟩
  rw [walkPure_congr_sibs h _ (honestSibs h z0 L i) H 0 i x
    (fun l _ hl => FullMerkle.pathSibs_honest h z0 L H i l (by omega))]
  exact hA.recompute

/-- **No located break on the contract's own path.**  The `HonestProofNoBreak` argument,
for the stream `Merkle.calculateRoot` reads from `merklePath(i)`. -/
private lemma contract_path_no_break (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree)
    (H i : ℕ) (hi : i < T.leafCount) :
    ¬ TreeRootBreak h z0 hl T H
        (FullMerkle.pathSibs ((List.range H).map (honestSibs h z0 (leafHashes hl T) i)))
        ((List.range H).map (honestSibs h z0 (leafHashes hl T) i)).length i (T.leaf i) := by
  rw [List.length_map, List.length_range]
  intro hb
  cases hb with
  | wrongLength hh => exact heightBreak_not_tautology.1 _ _ _ _ _ _ _ hh
  | pathCollision _ hc =>
    obtain ⟨j, hj, hne, _⟩ := hc
    apply hne
    refine walkPair_honest h z0 (leafHashes hl T) _ j 0 i (hl (T.leaf i)) ?_ ?_
    · intro l _ hl'
      rw [FullMerkle.pathSibs_honest h z0 _ H i l (by omega), Nat.sub_zero]
      rfl
    · rw [levels_zero, zeros_zero, leafHashes_getD hi]
  | leafCollision _ hne _ => exact hne rfl
  | paddingHit hle _ => omega

theorem contract_proofs_at_stored_root (h : Hash) (hl : LeafHash) (S : CState)
    (hS : CReaches h hl S) :
    ∃ R : UInt256, S.root = some R
      ∧ (∀ v : UInt256, v ∈ keys (toAbs S.tree) →
          ∃ i < S.tree.leafCount, (S.tree.leaf i).value = v
            ∧ ∃ p : List UInt256, S.merklePath i = some p ∧ p.length = S.fm.height
              ∧ InclusionAccepted h hl R v (S.tree.leaf i) i (FullMerkle.pathSibs p) p.length
              ∧ ¬ TreeRootBreak h (zeroLeafHash hl) hl S.tree S.fm.height (FullMerkle.pathSibs p)
                  p.length i (S.tree.leaf i))
      ∧ (∀ v : UInt256, v ≠ 0 → v ∉ keys (toAbs S.tree) →
          ∃ i < S.tree.leafCount,
            ∃ p : List UInt256, S.merklePath i = some p ∧ p.length = S.fm.height
              ∧ NonInclusionAccepted h hl R v (S.tree.leaf i) i (FullMerkle.pathSibs p) p.length
              ∧ ¬ TreeRootBreak h (zeroLeafHash hl) hl S.tree S.fm.height (FullMerkle.pathSibs p)
                  p.length i (S.tree.leaf i))
      ∧ (∀ (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256) (k₁ k₂ : ℕ),
          InclusionAccepted h hl R v ℓ₁ i₁ s₁ k₁ → NonInclusionAccepted h hl R v ℓ₂ i₂ s₂ k₂ →
            TreeRootBreak h (zeroLeafHash hl) hl S.tree S.fm.height s₁ k₁ i₁ ℓ₁
              ∨ TreeRootBreak h (zeroLeafHash hl) hl S.tree S.fm.height s₂ k₂ i₂ ℓ₂) := by
  obtain ⟨hH, hR, hroot⟩ := cReaches_root_is_published h hl S hS
  obtain ⟨c1, c2, c3⟩ := proofs_exclusive_or_break_at_own_height h (zeroLeafHash hl) hl S.toH hH
  refine ⟨_, hroot, ?_, ?_, c3⟩
  · intro v hv
    obtain ⟨i, hi, hval, hI, _⟩ := c1 v hv
    refine ⟨i, hi, hval, _, contract_path hR hi, by rw [List.length_map, List.length_range],
      ⟨hI.valueMatch, pathAccepts_contract hI.path⟩,
      contract_path_no_break h (zeroLeafHash hl) hl S.tree S.fm.height i hi⟩
  · intro v hv0 habs
    obtain ⟨i, hi, hN, _⟩ := c2 v hv0 habs
    refine ⟨i, hi, _, contract_path hR hi, by rw [List.length_map, List.length_range],
      ⟨hN.nonzero, hN.lowBelow, hN.window, pathAccepts_contract hN.path⟩,
      contract_path_no_break h (zeroLeafHash hl) hl S.tree S.fm.height i hi⟩

/-! ## Anti-vacuity -/

theorem cThreeLeaf_witness (h : Hash) (hl : LeafHash) (a b : UInt256) (ha : 0 < a)
    (hab : a < b) :
    ∃ (S₀ S₁ S₂ : CState) (r₁ r₂ : UInt256),
      cSetup h hl = some S₀ ∧ cInsert h hl S₀ a 0 = some (S₁, r₁)
      ∧ cInsert h hl S₁ b 1 = some (S₂, r₂)
      ∧ CReaches h hl S₂ ∧ S₂.tree = threeLeafTree a b ∧ S₂.toH = hThree a b
      ∧ S₁.fm.height = 1 ∧ S₂.fm.height = 2 ∧ S₂.root = some r₂
      ∧ (∃ p : List UInt256, S₂.merklePath 1 = some p
          ∧ InclusionAccepted h hl r₂ a (S₂.tree.leaf 1) 1 (FullMerkle.pathSibs p) p.length)
      ∧ S₂.merklePath 3 = none
      ∧ NonInclusionAccepted h hl r₂ a ⟨0, 0, 0⟩ 3
          (honestSibs h (zeroLeafHash hl) (leafHashes hl S₂.tree) 3) 2
      ∧ TreeRootBreakExactly h (zeroLeafHash hl) hl S₂.tree 2
          (honestSibs h (zeroLeafHash hl) (leafHashes hl S₂.tree) 3) 2 3 ⟨0, 0, 0⟩ .paddingHit := by
  obtain ⟨hg₁, hg₂⟩ := threeLeafTree_guards ha hab
  obtain ⟨S₀, hs₀, htree₀, hH₀, _⟩ := cSetup_caches h hl
  have hc₀ : CReaches h hl S₀ := CReaches.init hs₀
  rw [← htree₀] at hg₁
  obtain ⟨S₁, r₁, hins₁, hc₁, htoH₁, _, _⟩ := cInsert_returns_published_root h hl S₀ a 0 hc₀ hg₁
  have htree₁ : S₁.tree = insert setup a 0 := by
    rw [show S₁.tree = S₁.toH.tree from rfl, htoH₁, hH₀]; rfl
  rw [← htree₁] at hg₂
  obtain ⟨S₂, r₂, hins₂, hc₂, htoH₂, hroot₂, hr₂⟩ :=
    cInsert_returns_published_root h hl S₁ b 1 hc₁ hg₂
  have hview : S₂.toH = hThree a b := by rw [htoH₂, htoH₁, hH₀]; rfl
  have htree₂ : S₂.tree = threeLeafTree a b := congrArg HState.tree hview
  have hheight₂ : S₂.fm.height = 2 := congrArg HState.height hview
  have hheight₁ : S₁.fm.height = 1 := by
    rw [show S₁.fm.height = S₁.toH.height from rfl, htoH₁, hH₀]; rfl
  have hr₂' : r₂ = (hThree a b).root h (zeroLeafHash hl) hl := by rw [hr₂, ← htoH₂, hview]
  obtain ⟨_, _, _, hI, hN, _, hX⟩ := padding_forgery_at_own_height h hl a b ha hab
  have hR₂ := (cReaches_caches hc₂).2
  refine ⟨S₀, S₁, S₂, r₁, r₂, hs₀, hins₁, hins₂, hc₂, htree₂, hview, hheight₁, hheight₂, hroot₂,
    ?_, ?_, ?_, ?_⟩
  · have hi : 1 < S₂.tree.leafCount := by rw [htree₂]; show 1 < 3; omega
    refine ⟨_, contract_path hR₂ hi, ?_⟩
    have hI' : InclusionAccepted h hl r₂ a (S₂.tree.leaf 1) 1
        (honestSibs h (zeroLeafHash hl) (leafHashes hl S₂.tree) 1) S₂.fm.height := by
      rwa [hr₂', htree₂, hheight₂]
    exact ⟨hI'.valueMatch, pathAccepts_contract hI'.path⟩
  · show FullMerkle.merklePath S₂.fm 3 = none
    refine FullMerkle.merklePath_out_of_range_reverts S₂.fm 3 ?_
    rw [hR₂.leafNumber_eq, leafHashes_length, htree₂]
    show 3 ≤ 3
    omega
  · rwa [hr₂', htree₂]
  · rwa [htree₂]

end Contracts.InteropCommitmentTree

/-! ## Certificates -/

namespace Contracts.InteropCommitmentTree

theorem CSetupCaches : Properties.CSetupCaches := cSetup_caches
theorem CInsertCaches : Properties.CInsertCaches := cInsert_caches
theorem CReachesRootIsPublished : Properties.CReachesRootIsPublished := cReaches_root_is_published
theorem CRunRootIsPublished : Properties.CRunRootIsPublished := cRun_root_is_published
theorem CInsertReturnsPublishedRoot : Properties.CInsertReturnsPublishedRoot :=
  cInsert_returns_published_root
theorem CInsertReturnsTheWalk : Properties.CInsertReturnsTheWalk := cInsert_returns_the_walk
theorem HReachesLifts : Properties.HReachesLifts := hReaches_lifts
theorem HRunLiftsToCRun : Properties.HRunLiftsToCRun := hRun_lifts_to_cRun
theorem ContractProofsAtStoredRoot : Properties.ContractProofsAtStoredRoot :=
  contract_proofs_at_stored_root
theorem CThreeLeafWitness : Properties.CThreeLeafWitness := cThreeLeaf_witness

end Contracts.InteropCommitmentTree
