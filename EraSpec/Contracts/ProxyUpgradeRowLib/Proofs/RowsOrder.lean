import EraSpec.Contracts.ProxyUpgradeRowLib.Properties.RowsOrder
import EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsUnvalidated

/-!
# Proofs: which row orders succeed

The positive result rests on one commutation lemma, `applyRow_comm`: two rows on distinct
proxies can run in either order, to the same state. Under `ReinitFrames` a row's iteration
leaves the other row's proxy alone (`applyRow_frame`), so each row takes the same branch in
either order. Under `ReinitReadsOwnProxy` the value a swap leaves at its own proxy does not
depend on the state it starts from (`swap_own_const`), so two swaps commute (`swap_comm`).
Induction on the permutation then moves the whole loop (`applyLoop_perm`). The countermodels
are computations, with determinism (`applyLoop_det`) for the reverting order.
-/

namespace Contracts.ProxyUpgradeCurrent

/-! ## Swaps -/

/-- Under `ReinitReadsOwnProxy`, where a row's swap leaves its own proxy does not depend on
the state it starts from: the swap first puts the proxy at `implNew`. -/
lemma swap_own_const {C : Config} (hl : ReinitReadsOwnProxy C) (r : Row) (I I' : Impl) :
    swap C r I r.proxy = swap C r I' r.proxy := by
  unfold swap
  split
  · exact hl r _ _ (by rw [upd_same, upd_same])
  · rw [upd_same, upd_same]

/-- Two swaps on distinct proxies commute. -/
lemma swap_comm {C : Config} (hf : ReinitFrames C) (hl : ReinitReadsOwnProxy C) {x y : Row}
    (hxy : x.proxy ≠ y.proxy) (I : Impl) : swap C y (swap C x I) = swap C x (swap C y I) := by
  funext q
  by_cases hqx : q = x.proxy
  · subst hqx
    rw [swap_frame hf (I := swap C x I) hxy]
    exact swap_own_const hl x I (swap C y I)
  · by_cases hqy : q = y.proxy
    · subst hqy
      rw [swap_frame hf (I := swap C y I) hqx]
      exact swap_own_const hl y (swap C x I) I
    · rw [swap_frame hf (I := swap C x I) hqy, swap_frame hf (I := I) hqx,
        swap_frame hf (I := swap C y I) hqx, swap_frame hf (I := I) hqy]

/-! ## Rows and loops -/

/-- Two rows on distinct proxies can run in either order, to the same state. -/
lemma applyRow_comm {C : Config} (hf : ReinitFrames C) (hl : ReinitReadsOwnProxy C)
    {x y : Row} (hxy : x.proxy ≠ y.proxy) {I J K : Impl} (h1 : ApplyRow C I x J)
    (h2 : ApplyRow C J y K) : ∃ J', ApplyRow C I y J' ∧ ApplyRow C J' x K := by
  cases h1 with
  | alreadyAtTarget hx =>
      exact ⟨K, h2, ApplyRow.alreadyAtTarget ((applyRow_frame hf h2 x.proxy hxy).trans hx)⟩
  | upgrade ho hne hsrc =>
      -- `y` finds its proxy where it was before `x`'s swap.
      have hy : swap C x I y.proxy = I y.proxy := swap_frame hf (Ne.symm hxy)
      cases h2 with
      | alreadyAtTarget hyt =>
          exact ⟨I, ApplyRow.alreadyAtTarget (hy.symm.trans hyt), ApplyRow.upgrade ho hne hsrc⟩
      | upgrade ho' hne' hsrc' =>
          refine ⟨swap C y I, ApplyRow.upgrade ho' (fun h => hne' (hy.trans h))
            (hy.symm.trans hsrc'), ?_⟩
          rw [swap_comm hf hl hxy I]
          have hx : swap C y I x.proxy = I x.proxy := swap_frame hf hxy
          exact ApplyRow.upgrade ho (fun h => hne (hx.symm.trans h)) (hx.trans hsrc)

/-- Under the three premises, the loop over a permutation of rows naming distinct proxies
reaches the same state. -/
lemma applyLoop_perm {C : Config} (hf : ReinitFrames C) (hl : ReinitReadsOwnProxy C)
    {rows rows' : List Row} (hp : rows.Perm rows') :
    ∀ {I K : Impl}, rows.Pairwise (fun a b => a.proxy ≠ b.proxy) →
      ApplyLoop C I rows K → ApplyLoop C I rows' K := by
  induction hp with
  | nil => exact fun _ h => h
  | cons x _ ih =>
      intro I K hd h
      cases h with
      | cons hstep hrest => exact ApplyLoop.cons hstep (ih (List.pairwise_cons.mp hd).2 hrest)
  | swap x y l =>
      intro I K hd h
      have hyx : y.proxy ≠ x.proxy := (List.pairwise_cons.mp hd).1 x List.mem_cons_self
      cases h with
      | cons h1 hrest =>
          cases hrest with
          | cons h2 hrest' =>
              obtain ⟨J', h1', h2'⟩ := applyRow_comm hf hl hyx h1 h2
              exact ApplyLoop.cons h1' (ApplyLoop.cons h2' hrest')
  | trans h12 _ ih12 ih23 =>
      intro I K hd h
      exact ih23 ((h12.pairwise_iff fun h => Ne.symm h).mp hd) (ih12 hd h)

end Contracts.ProxyUpgradeCurrent

/-! ## Certificates -/

namespace Contracts.ProxyUpgradeCurrent

theorem DistinctRowsApplyInAnyOrder : Properties.DistinctRowsApplyInAnyOrder := by
  intro C I J rows rows' hp hd hf hl h
  exact ⟨fun r hr => h.code r (hp.mem_iff.mpr hr), applyLoop_perm hf hl hp hd h.loop,
    fun r hr => h.verified r (hp.mem_iff.mpr hr)⟩

end Contracts.ProxyUpgradeCurrent

/-! ## Countermodels and the witness -/

namespace Contracts.ProxyUpgradeCurrent

lemma valid_BA : ValidRows [rowB, rowA] :=
  ⟨by simp [rowA, rowB], by simp [rowA, rowB], by simp [rowA, rowB]⟩

lemma valid_A2B : ValidRows [rowA2, rowB] :=
  ⟨by simp [rowA2, rowB], by simp [rowA2, rowB], by simp [rowA2, rowB]⟩

lemma readsOther_frames : ReinitFrames wReadsOtherProxy := by
  intro r I q hq
  show (if r = rowB then (if I 5 = 11 then I else upd I 6 10) else I) q = I q
  split_ifs with h
  · rfl
  · subst h; exact upd_ne _ _ hq
  · rfl

/-- Two states with proxy `6` at `12` that differ at proxy `5`: `rowB`'s reinitializer keeps
proxy `6` at `12` in the first and moves it to `10` in the second. -/
lemma readsOther_not_own : ¬ ReinitReadsOwnProxy wReadsOtherProxy :=
  fun hl => absurd (hl rowB (upd (upd wImpl 5 11) 6 12) (upd wImpl 6 12) (by decide))
    (by decide)

lemma leakNamed_reads_own : ReinitReadsOwnProxy wLeakNamed := by
  intro r I I' h
  show (if r = rowB then upd I 5 11 else I) r.proxy = (if r = rowB then upd I' 5 11 else I') r.proxy
  split_ifs with hr
  · subst hr
    have hne : rowB.proxy ≠ 5 := by decide
    rw [upd_ne I 11 hne, upd_ne I' 11 hne]
    exact h
  · exact h

theorem ReinitReadBreaksOrder : Properties.ReinitReadBreaksOrder := by
  have hloopBA : ApplyLoop wReadsOtherProxy wImpl [rowB, rowA]
      (swap wReadsOtherProxy rowA (swap wReadsOtherProxy rowB wImpl)) :=
    ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide))
      (ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide)) ApplyLoop.nil)
  refine ⟨readsOther_frames, readsOther_not_own, valid_AB, valid_BA, List.Perm.swap _ _ _,
    ⟨swap wReadsOtherProxy rowB (swap wReadsOtherProxy rowA wImpl),
      code_all wReadsOtherProxy (fun _ => trivial) _,
      ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide))
        (ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide)) ApplyLoop.nil), ?_⟩, ?_⟩
  · intro r hr; rcases mem_AB hr with rfl | rfl <;> decide
  · rintro ⟨K, h⟩
    have h6 := h.verified rowB (by simp)
    rw [applyLoop_det h.loop hloopBA] at h6
    exact absurd h6 (by decide)

theorem ReinitLeakBreaksOrder : Properties.ReinitLeakBreaksOrder := by
  obtain ⟨-, -, -, J, hJ, -⟩ := ReinitLeakMovesNamedProxyOffEdge
  exact ⟨leakNamed_not_frames, leakNamed_reads_own, valid_BA2, valid_A2B, List.Perm.swap _ _ _,
    ⟨J, hJ⟩, StaleObjectReverts wLeakNamed wImpl rowA2 [rowB] (by decide) (by decide)⟩

theorem RowsOrderWitness : Properties.RowsOrderWitness :=
  ⟨wConfig_frames, fun _ _ _ h => h, valid_AB.distinctProxies, List.Perm.swap _ _ _, rfl,
    _, applyRows_AB, fun h => absurd (congrFun h 5) (by decide)⟩

end Contracts.ProxyUpgradeCurrent
