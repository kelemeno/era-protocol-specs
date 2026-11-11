import EraSpec.Contracts.ProxyUpgradeRowLib.Properties.RowsUnvalidated
import EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsCurrent

/-!
# Proofs: rows that `validateRows` never checked

The headline rests on one loop lemma, `applyLoop_first`: under `ReinitFrames`, rows naming
other proxies leave a proxy alone (`applyRow_frame`), so the first row naming it finds it
where the call started, at the row's target or its source. The verification field of
`ApplyRows` then says the proxy ends at that row's target. Proxies no row names are framed by
`applyLoop_frame`. The reading of the source's `@dev` (`ReinitMovesAreCaughtOnLastRow`) adds
a split of the loop at a row (`applyLoop_append`) and determinism; the distinct-rows form is
its corollary. The countermodels and witnesses are computations.
-/

namespace Contracts.ProxyUpgradeCurrent

/-! ## Lists -/

/-- A list with an element satisfying `P` splits at the first such element. -/
lemma exists_first_split {P : Row → Prop} :
    ∀ {rows : List Row}, (∃ r ∈ rows, P r) →
      ∃ pre r post, rows = pre ++ r :: post ∧ P r ∧ ∀ x ∈ pre, ¬ P x
  | [], ⟨_, hr, _⟩ => absurd hr List.not_mem_nil
  | y :: ys, ⟨r, hr, hp⟩ => by
      by_cases hy : P y
      · exact ⟨[], y, ys, rfl, hy, fun _ hx => absurd hx List.not_mem_nil⟩
      · have hr' : r ∈ ys := by
          rcases List.mem_cons.mp hr with rfl | h
          · exact absurd hp hy
          · exact h
        obtain ⟨pre, r', post, hsplit, hp', hpre⟩ := exists_first_split ⟨r, hr', hp⟩
        refine ⟨y :: pre, r', post, by rw [hsplit]; rfl, hp', fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hy
        · exact hpre x hx'

/-! ## The loop -/

/-- The loop over `xs ++ ys` runs `xs`, then `ys`. -/
lemma applyLoop_append {C : Config} {ys : List Row} :
    ∀ {xs : List Row} {I J : Impl}, ApplyLoop C I (xs ++ ys) J →
      ∃ K, ApplyLoop C I xs K ∧ ApplyLoop C K ys J
  | [], I, _, h => ⟨I, ApplyLoop.nil, h⟩
  | x :: xs, _, _, h => by
      rw [List.cons_append] at h
      cases h with
      | cons hstep hrest =>
          obtain ⟨K, h1, h2⟩ := applyLoop_append hrest
          exact ⟨K, ApplyLoop.cons hstep h1, h2⟩

/-- Under `ReinitFrames`, the first row naming a proxy finds it where the call started: at
the row's target (it is skipped) or at its source (it is upgraded). No premise on the rows. -/
lemma applyLoop_first {C : Config} (hf : ReinitFrames C) {r : Row} {post : List Row} :
    ∀ {pre : List Row} {I J : Impl}, ApplyLoop C I (pre ++ r :: post) J →
      (∀ x ∈ pre, x.proxy ≠ r.proxy) → I r.proxy = r.implNew ∨ I r.proxy = r.expectedOldImpl
  | [], _, _, h, _ => by
      cases h with
      | cons hstep _ =>
          cases hstep with
          | alreadyAtTarget he => exact Or.inl he
          | upgrade _ _ hsrc => exact Or.inr hsrc
  | x :: pre, _, _, h, hpre => by
      rw [List.cons_append] at h
      cases h with
      | cons hstep hrest =>
          rw [← applyRow_frame hf hstep r.proxy
            (fun hq => hpre x List.mem_cons_self hq.symm)]
          exact applyLoop_first hf hrest (fun y hy => hpre y (List.mem_cons_of_mem _ hy))

/-- The first row naming a proxy carries its edge, for a whole call. -/
lemma applyRows_first {C : Config} (hf : ReinitFrames C) {I J : Impl} {pre post : List Row}
    {r : Row} (h : ApplyRows C I (pre ++ r :: post) J) (hpre : ∀ x ∈ pre, x.proxy ≠ r.proxy) :
    (I r.proxy = r.implNew ∨ I r.proxy = r.expectedOldImpl) ∧ J r.proxy = r.implNew :=
  ⟨applyLoop_first hf h.loop hpre, h.verified r (List.mem_append_right pre List.mem_cons_self)⟩

end Contracts.ProxyUpgradeCurrent

/-! ## Certificates -/

namespace Contracts.ProxyUpgradeCurrent

theorem OnlyNamedEdgesAcrossCallAnyRows : Properties.OnlyNamedEdgesAcrossCallAnyRows := by
  intro C I J rows hf h p
  by_cases hp : ∃ r ∈ rows, r.proxy = p
  · obtain ⟨pre, r, post, rfl, rfl, hpre⟩ := exists_first_split hp
    obtain ⟨hstart, hend⟩ := applyRows_first hf h hpre
    rcases hstart with h1 | h1
    · exact Or.inl (hend.trans h1.symm)
    · exact Or.inr ⟨r, List.mem_append_right pre List.mem_cons_self, rfl, h1, hend⟩
  · exact Or.inl (applyLoop_frame hf h.loop p (fun r hr hq => hp ⟨r, hr, hq⟩))

theorem FirstRowCarriesTheEdge : Properties.FirstRowCarriesTheEdge :=
  fun _ _ _ _ _ _ hf h hpre => applyRows_first hf h hpre

theorem OnlyNamedEdgesAcrossTransitionAnyRows : Properties.OnlyNamedEdgesAcrossTransitionAnyRows :=
  fun C _ T I J hf h => OnlyNamedEdgesAcrossCallAnyRows C I J T.rows hf h.2.2

theorem SourceIsNotAppliedAnyRows : Properties.SourceIsNotAppliedAnyRows := by
  intro C I J rows r hr hne hs
  refine ⟨fun ha => hne (hs.symm.trans (ha r hr)), fun h => ?_⟩
  rw [h.verified r hr, hs]
  exact hne.symm

theorem ReinitMovesAreCaughtOnLastRow : Properties.ReinitMovesAreCaughtOnLastRow := by
  intro C I J K L pre post r hf h hK hL hpost
  obtain ⟨K', h1, h2⟩ := applyLoop_append h.loop
  rw [applyLoop_det h1 hK] at h2
  cases h2 with
  | cons hstep hrest =>
      rw [applyRow_det hstep hL] at hrest
      -- No row after `r` names `r`'s proxy, so it ends where `r`'s iteration left it.
      have hat : L r.proxy = r.implNew := by
        rw [← applyLoop_frame hf hrest r.proxy hpost]
        exact h.verified r (List.mem_append_right pre List.mem_cons_self)
      funext q
      by_cases hq : q = r.proxy
      · subst hq
        rw [hat, upd_same]
      · rw [upd_ne _ _ hq]
        exact applyRow_frame hf hL q hq

theorem ReinitMovesAreCaughtOnDistinctRows : Properties.ReinitMovesAreCaughtOnDistinctRows :=
  fun C I J K L pre post r hd hf h hK hL =>
    ReinitMovesAreCaughtOnLastRow C I J K L pre post r hf h hK hL fun x hx hq =>
      (List.pairwise_cons.mp (List.pairwise_append.mp hd).2.1).1 x hx hq.symm

end Contracts.ProxyUpgradeCurrent

/-! ## Countermodels and witnesses -/

namespace Contracts.ProxyUpgradeCurrent

lemma valid_B : ValidRows [rowB] :=
  ⟨by simp [rowB], by simp [rowB], by simp⟩

lemma valid_B2 : ValidRows [rowB2] :=
  ⟨by simp [rowB2], by simp [rowB2], by simp⟩

lemma valid_B3 : ValidRows [rowB3] :=
  ⟨by simp [rowB3], by simp [rowB3], by simp⟩

lemma valid_BA2 : ValidRows [rowB, rowA2] :=
  ⟨by simp [rowB, rowA2], by simp [rowB, rowA2], by simp [rowB, rowA2]⟩

lemma detour_frames : ReinitFrames wDetour := by
  intro r I q hq
  show (if r = rowB then upd I 6 11 else I) q = I q
  split_ifs with h
  · subst h; exact upd_ne _ _ hq
  · rfl

lemma leakNamed_not_frames : ¬ ReinitFrames wLeakNamed :=
  fun hf => absurd (hf rowB wImpl 5 (by decide)) (by decide)

/-- Rows naming proxy `6` twice (`rowB`, then `rowB2`) are not pairwise distinct. -/
lemma not_distinct_BB2 : ¬ [rowB, rowB2].Pairwise (fun a b => a.proxy ≠ b.proxy) :=
  fun hd => (List.pairwise_cons.mp hd).1 rowB2 (by simp) rfl

/-- Membership in a two-row list, as two cases. -/
lemma mem_pair {a b r : Row} (hr : r ∈ [a, b]) : r = a ∨ r = b := by
  simpa using hr

/-- The non-genuine rows apply under the detouring reinitializer: `rowB` moves proxy `6` to
`12` and its reinitializer on to `11`; `rowB2` moves it from `11` to `12`. -/
lemma applyRows_dup_detour :
    ApplyRows wDetour wImpl [rowB, rowB2] (swap wDetour rowB2 (swap wDetour rowB wImpl)) := by
  refine ⟨code_all wDetour (fun _ => trivial) _,
    ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide))
      (ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide)) ApplyLoop.nil), ?_⟩
  intro r hr; rcases mem_pair hr with rfl | rfl <;> decide

/-- The same rows under the inert witness configuration: `rowB` moves proxy `6` to `12`, and
`rowB2` is skipped. -/
lemma applyRows_dup_wConfig :
    ApplyRows wConfig wImpl [rowB, rowB2] (swap wConfig rowB wImpl) := by
  refine ⟨code_all wConfig (fun _ => trivial) _,
    ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide))
      (ApplyLoop.cons (ApplyRow.alreadyAtTarget (by decide)) ApplyLoop.nil), ?_⟩
  intro r hr; rcases mem_pair hr with rfl | rfl <;> decide

theorem LaterDuplicateRowIsNotAnEdgeFromStart :
    Properties.LaterDuplicateRowIsNotAnEdgeFromStart := by
  refine ⟨wConfig_frames, fun hd => (List.pairwise_cons.mp hd).1 rowA3 (by simp) rfl,
    DuplicateRowsBreakOrder.2.2.2.1, fun hall => ?_⟩
  rcases hall rowA3 (by simp) with h | h <;> exact absurd h (by decide)

theorem DuplicateRowHidesReinitMove : Properties.DuplicateRowHidesReinitMove := by
  have hstep : ApplyRow wDetour wImpl rowB (swap wDetour rowB wImpl) :=
    ApplyRow.upgrade rfl (by decide) (by decide)
  refine ⟨detour_frames, valid_B, valid_B2, not_distinct_BB2, ?_, ⟨_, applyRows_dup_detour⟩,
    _, hstep, by decide⟩
  rintro ⟨J, h⟩
  have h6 := h.verified rowB (by simp)
  rw [applyLoop_det h.loop (ApplyLoop.cons hstep ApplyLoop.nil)] at h6
  exact absurd h6 (by decide)

theorem DetourThenSkipIsCaught : Properties.DetourThenSkipIsCaught := by
  refine ⟨detour_frames, valid_B3,
    ⟨_, ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide))
      (ApplyLoop.cons (ApplyRow.alreadyAtTarget (by decide)) ApplyLoop.nil), by decide⟩, ?_⟩
  exact TwoTargetsForOneProxyRevert wDetour wImpl [rowB, rowB3] rowB rowB3
    (by simp) (by simp) rfl (by decide)

theorem ReinitLeakMovesNamedProxyOffEdge : Properties.ReinitLeakMovesNamedProxyOffEdge := by
  have hloop : ApplyLoop wLeakNamed wImpl [rowB, rowA2]
      (swap wLeakNamed rowA2 (swap wLeakNamed rowB wImpl)) :=
    ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide))
      (ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide)) ApplyLoop.nil)
  refine ⟨leakNamed_not_frames, valid_BA2,
    ⟨_, ApplyRow.upgrade rfl (by decide) (by decide), by decide⟩,
    swap wLeakNamed rowA2 (swap wLeakNamed rowB wImpl),
    ⟨code_all wLeakNamed (fun _ => trivial) _, hloop, ?_⟩, by simp, rfl, ?_⟩
  · intro r hr; rcases mem_pair hr with rfl | rfl <;> decide
  · rintro (h | ⟨r, hr, hp, hsrc, _⟩)
    · exact absurd h (by decide)
    · rcases mem_pair hr with rfl | rfl
      · exact absurd hp (by decide)
      · exact absurd hsrc (by decide)

theorem AnyRowsWitness : Properties.AnyRowsWitness := by
  refine ⟨detour_frames, fun hg => not_distinct_BB2 hg.2.distinctProxies, not_distinct_BB2,
    List.mem_cons_self, by decide, rfl, swap wDetour rowB2 (swap wDetour rowB wImpl),
    ⟨trivial, rfl, applyRows_dup_detour⟩, applyRows_dup_detour, by decide, by decide, ?_⟩
  intro q hq
  have hq2 : q ≠ rowB2.proxy := hq
  rw [swap_frame detour_frames hq2, swap_frame detour_frames hq]

theorem ReinitMovesCaughtWitness : Properties.ReinitMovesCaughtWitness := by
  refine ⟨wConfig_frames, valid_AB.distinctProxies, rfl,
    ⟨_, swap wConfig rowA wImpl, _, applyRows_AB,
      ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide)) ApplyLoop.nil,
      ApplyRow.upgrade rfl (by decide) (by decide), by decide⟩,
    detour_frames, not_distinct_BB2,
    _, swap wDetour rowB wImpl, _, applyRows_dup_detour,
    ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide)) ApplyLoop.nil,
    ApplyRow.upgrade rfl (by decide) (by decide), by decide⟩

end Contracts.ProxyUpgradeCurrent
