import EraSpec.Contracts.ProxyUpgradeRowLib.Properties.RowsCurrent

/-!
# Proofs: the proxy rows at `e561b9cc2`

The verification pass makes the post-state a field of `ApplyRows`, so the postcondition,
idempotence and the two-targets revert are immediate. The frame results rest on one loop
lemma (`applyLoop_frame`, under `ReinitFrames`), and replay safety for the whole call on a
second (`applyLoop_source`: under distinct proxies, each row finds its proxy at its source
or its target). The countermodels are computations.
-/

namespace Contracts.ProxyUpgradeCurrent

/-! ## Mappings and swaps -/

@[simp] lemma upd_same (f : Impl) (p v : Address) : upd f p v p = v := by simp [upd]

lemma upd_ne (f : Impl) {q p : Address} (v : Address) (h : q ≠ p) : upd f p v q = f q := by
  simp [upd, h]

lemma swap_frame {C : Config} (hf : ReinitFrames C) {r : Row} {I : Impl} {q : Address}
    (hq : q ≠ r.proxy) : swap C r I q = I q := by
  unfold swap
  split
  · rw [hf r _ q hq]; exact upd_ne _ _ hq
  · exact upd_ne _ _ hq

lemma swap_inert {C : Config} {r : Row} (h : RowInert C r) (I : Impl) :
    swap C r I = upd I r.proxy r.implNew := by
  unfold swap
  rcases h with h | h
  · simp [h]
  · split
    · exact h _
    · rfl

/-! ## One row -/

lemma applyRow_frame {C : Config} (hf : ReinitFrames C) {I J : Impl} {r : Row}
    (h : ApplyRow C I r J) : ∀ q, q ≠ r.proxy → J q = I q := by
  intro q hq
  cases h with
  | alreadyAtTarget _ => rfl
  | upgrade _ _ _ => exact swap_frame hf hq

lemma applyRow_stale {C : Config} {I : Impl} {r : Row}
    (hsrc : I r.proxy ≠ r.expectedOldImpl) (htgt : I r.proxy ≠ r.implNew) :
    ¬ ∃ J, ApplyRow C I r J := by
  rintro ⟨J, h⟩
  cases h with
  | alreadyAtTarget he => exact htgt he
  | upgrade _ _ he => exact hsrc he

lemma applyRow_det {C : Config} {I J K : Impl} {r : Row}
    (h₁ : ApplyRow C I r J) (h₂ : ApplyRow C I r K) : J = K := by
  cases h₁ with
  | alreadyAtTarget he =>
      cases h₂ with
      | alreadyAtTarget _ => rfl
      | upgrade _ hne _ => exact absurd he hne
  | upgrade _ hne _ =>
      cases h₂ with
      | alreadyAtTarget he => exact absurd he hne
      | upgrade _ _ _ => rfl

/-! ## The loop -/

lemma applyLoop_det {C : Config} {I J K : Impl} {rows : List Row}
    (h₁ : ApplyLoop C I rows J) (h₂ : ApplyLoop C I rows K) : J = K := by
  induction h₁ generalizing K with
  | nil => cases h₂ with | nil => rfl
  | cons hstep _ ih =>
      cases h₂ with
      | cons hstep' hrest' =>
          exact ih (by rw [applyRow_det hstep hstep']; exact hrest')

lemma applyLoop_frame {C : Config} (hf : ReinitFrames C) {I J : Impl} {rows : List Row}
    (h : ApplyLoop C I rows J) : ∀ p, (∀ r ∈ rows, r.proxy ≠ p) → J p = I p := by
  induction h with
  | nil => intro _ _; rfl
  | @cons I J K r rs hstep _ ih =>
      intro p hp
      rw [ih p (fun t ht => hp t (List.mem_cons_of_mem _ ht))]
      exact applyRow_frame hf hstep p (fun hq => hp r (List.mem_cons_self _ _) hq.symm)

/-- Under distinct proxies, each row finds its proxy at its target or its source: no
earlier row has touched it. -/
lemma applyLoop_source {C : Config} (hf : ReinitFrames C) {I J : Impl} {rows : List Row}
    (h : ApplyLoop C I rows J) : rows.Pairwise (fun a b => a.proxy ≠ b.proxy) →
    ∀ r ∈ rows, I r.proxy = r.implNew ∨ I r.proxy = r.expectedOldImpl := by
  induction h with
  | nil => intro _ r hr; exact absurd hr (List.not_mem_nil r)
  | @cons I J K r rs hstep _ ih =>
      intro hd t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · cases hstep with
        | alreadyAtTarget he => exact Or.inl he
        | upgrade _ _ hsrc => exact Or.inr hsrc
      · have hne : t.proxy ≠ r.proxy := fun hq => (List.pairwise_cons.mp hd).1 t ht' hq.symm
        rw [← applyRow_frame hf hstep t.proxy hne]
        exact ih (List.pairwise_cons.mp hd).2 t ht'

/-- From a state that already passes the verification, every row takes the skip. -/
lemma applyLoop_skip {C : Config} {I : Impl} {rows : List Row} (h : RowsApplied I rows) :
    ApplyLoop C I rows I := by
  induction rows with
  | nil => exact ApplyLoop.nil
  | cons r rs ih =>
      exact ApplyLoop.cons (ApplyRow.alreadyAtTarget (h r (List.mem_cons_self _ _)))
        (ih (fun t ht => h t (List.mem_cons_of_mem _ ht)))

lemma applyLoop_unowned {C : Config} (hne : C.adminOwner ≠ C.self) {I J : Impl}
    {rows : List Row} (h : ApplyLoop C I rows J) : J = I := by
  induction h with
  | nil => rfl
  | cons hstep _ ih =>
      cases hstep with
      | alreadyAtTarget _ => exact ih
      | upgrade ho _ _ => exact absurd ho hne

/-! ## The inventory -/

lemma mem_toRows {slots : List Row} {r : Row} : r ∈ toRows slots ↔ r ∈ slots ∧ r.implNew ≠ 0 := by
  simp [toRows, dropInertSlots, List.mem_filter]

lemma toRows_sublist (slots : List Row) : (toRows slots).Sublist slots :=
  List.filter_sublist _

end Contracts.ProxyUpgradeCurrent

/-! ## Certificates -/

namespace Contracts.ProxyUpgradeCurrent

theorem OnlyTheNamedEdge : Properties.OnlyTheNamedEdge := by
  intro C I J r hi h
  cases h with
  | alreadyAtTarget _ => exact ⟨fun _ _ => rfl, Or.inl rfl⟩
  | upgrade _ _ hsrc =>
      rw [swap_inert hi]
      exact ⟨fun q hq => upd_ne _ _ hq, Or.inr ⟨hsrc, upd_same _ _ _⟩⟩

theorem StaleObjectCannotDowngrade : Properties.StaleObjectCannotDowngrade :=
  fun _ _ _ hsrc htgt => applyRow_stale hsrc htgt

theorem StaleObjectReverts : Properties.StaleObjectReverts := by
  rintro C I r rs hsrc htgt ⟨J, ⟨_, hl, _⟩⟩
  cases hl with
  | cons hstep _ => exact applyRow_stale hsrc htgt ⟨_, hstep⟩

theorem ApplyRowsDeterministic : Properties.ApplyRowsDeterministic :=
  fun _ _ _ _ _ h₁ h₂ => applyLoop_det h₁.loop h₂.loop

theorem ApplyRowsPostcondition : Properties.ApplyRowsPostcondition :=
  fun _ _ _ _ h => h.verified

theorem ApplyRowsIdempotent : Properties.ApplyRowsIdempotent :=
  fun _ _ _ _ h => ⟨h.code, applyLoop_skip h.verified, h.verified⟩

theorem AppliedGatePasses : Properties.AppliedGatePasses :=
  fun _ _ _ _ _ h hframe r hr => (hframe r hr).trans (h.verified r hr)

theorem TwoTargetsForOneProxyRevert : Properties.TwoTargetsForOneProxyRevert := by
  rintro C I rows a b ha hb hab hne ⟨J, h⟩
  have h1 := h.verified a ha
  have h2 := h.verified b hb
  rw [hab, h2] at h1
  exact hne h1.symm

theorem UnownedAdminMovesNothing : Properties.UnownedAdminMovesNothing :=
  fun _ _ _ _ hne h => applyLoop_unowned hne h.loop

theorem UnmovedProxiesFrame : Properties.UnmovedProxiesFrame :=
  fun _ _ _ _ hf h => applyLoop_frame hf h.loop

theorem OnlyNamedEdgesAcrossCall : Properties.OnlyNamedEdgesAcrossCall := by
  intro C I J rows hd hf h p
  by_cases hp : ∃ r ∈ rows, r.proxy = p
  · obtain ⟨r, hr, rfl⟩ := hp
    rcases applyLoop_source hf h.loop hd r hr with h1 | h1
    · exact Or.inl ((h.verified r hr).trans h1.symm)
    · exact Or.inr ⟨r, hr, rfl, h1, h.verified r hr⟩
  · exact Or.inl (applyLoop_frame hf h.loop p (fun r hr hq => hp ⟨r, hr, hq⟩))

theorem OrderIndependent : Properties.OrderIndependent := by
  intro C I J K rows rows' hperm hf h h'
  funext p
  by_cases hp : ∃ r ∈ rows, r.proxy = p
  · obtain ⟨r, hr, rfl⟩ := hp
    rw [h.verified r hr, h'.verified r (hperm.mem_iff.mp hr)]
  · have hall : ∀ r ∈ rows, r.proxy ≠ p := fun r hr hq => hp ⟨r, hr, hq⟩
    rw [applyLoop_frame hf h.loop p hall,
      applyLoop_frame hf h'.loop p (fun r hr => hall r (hperm.mem_iff.mpr hr))]

theorem OrderIndependentOnRowProxies : Properties.OrderIndependentOnRowProxies := by
  intro C I J K rows rows' hperm h h' r hr
  rw [h.verified r hr, h'.verified r (hperm.mem_iff.mp hr)]

theorem ValidSourceIsNotApplied : Properties.ValidSourceIsNotApplied := by
  intro C I J rows r hv hr hs
  refine ⟨fun ha => hv.noSelfEdge r hr (hs.symm.trans (ha r hr)), fun h => ?_⟩
  rw [h.verified r hr, hs]
  exact (hv.noSelfEdge r hr).symm

theorem ToRowsKeepsActiveSlots : Properties.ToRowsKeepsActiveSlots :=
  fun slots _ => ⟨mem_toRows, toRows_sublist slots⟩

theorem InertSlotNeverUpgraded : Properties.InertSlotNeverUpgraded := by
  intro C I J slots s hf _ _ hother h
  refine applyLoop_frame hf h.loop s.proxy ?_
  intro t ht hq
  exact (mem_toRows.mp ht).2 (hother t (mem_toRows.mp ht).1 hq)

theorem WrongDomainTransitionReverts : Properties.WrongDomainTransitionReverts := by
  rintro C d T I hd ⟨J, _, h, _⟩
  exact hd h

end Contracts.ProxyUpgradeCurrent

/-! ## Countermodels and the witness -/

namespace Contracts.ProxyUpgradeCurrent

lemma valid_A : ValidRows [rowA] :=
  ⟨by simp [rowA], by simp [rowA], by simp⟩

lemma valid_A2 : ValidRows [rowA2] :=
  ⟨by simp [rowA2], by simp [rowA2], by simp⟩

lemma valid_A3 : ValidRows [rowA3] :=
  ⟨by simp [rowA3], by simp [rowA3], by simp⟩

lemma valid_AB : ValidRows [rowA, rowB] :=
  ⟨by simp [rowA, rowB], by simp [rowA, rowB], by simp [rowA, rowB]⟩

lemma code_all (C : Config) (hc : ∀ a, C.hasCode a) (rows : List Row) : RowCode C rows :=
  fun r _ => hc r.implNew

lemma wConfig_frames : ReinitFrames wConfig := fun _ _ _ _ => rfl

theorem SelfEdgeAppliesWithoutMoving : Properties.SelfEdgeAppliesWithoutMoving := by
  have happ : RowsApplied wImpl [rowSelf] := by
    intro r hr
    rw [List.mem_singleton.mp hr]; rfl
  refine ⟨⟨by simp [rowSelf], by simp⟩, fun hv => ?_, rfl, happ,
    ⟨code_all wConfig (fun _ => trivial) _, applyLoop_skip happ, happ⟩⟩
  exact hv.noSelfEdge rowSelf (List.mem_singleton_self _) rfl

theorem DuplicateRowsNowRevert : Properties.DuplicateRowsNowRevert := by
  refine ⟨valid_A, valid_A2, ⟨_, ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide))
    (ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide)) ApplyLoop.nil), ?_⟩, ?_⟩
  · intro hall
    exact absurd (hall rowA (by simp)) (by decide)
  · exact TwoTargetsForOneProxyRevert wConfig wImpl [rowA, rowA2] rowA rowA2
      (by simp) (by simp) rfl (by decide)

theorem DuplicateRowsBreakOrder : Properties.DuplicateRowsBreakOrder := by
  refine ⟨valid_A, valid_A3, fun hd => (List.pairwise_cons.mp hd).1 rowA3 (by simp) rfl, ?_, ?_⟩
  · refine ⟨_, code_all wConfig (fun _ => trivial) _,
      ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide))
        (ApplyLoop.cons (ApplyRow.alreadyAtTarget (by decide)) ApplyLoop.nil), ?_⟩
    intro r hr
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  · exact StaleObjectReverts wConfig wImpl rowA3 [rowA] (by decide) (by decide)

lemma selfMoving_frames : ReinitFrames wSelfMoving := by
  intro r I q hq
  show (if r = rowB then upd I 6 10 else I) q = I q
  split_ifs with h
  · subst h; exact upd_ne _ _ hq
  · rfl

/-- Membership in the two-row list, as two cases. -/
lemma mem_AB {r : Row} (hr : r ∈ [rowA, rowB]) : r = rowA ∨ r = rowB := by
  simpa using hr

theorem ReinitMovingOwnProxyIsCaught : Properties.ReinitMovingOwnProxyIsCaught := by
  have hloop : ApplyLoop wSelfMoving wImpl [rowA, rowB]
      (swap wSelfMoving rowB (swap wSelfMoving rowA wImpl)) :=
    ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide))
      (ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide)) ApplyLoop.nil)
  refine ⟨selfMoving_frames, valid_AB, ⟨_, hloop⟩, ?_⟩
  rintro ⟨J, h⟩
  have h6 := h.verified rowB (by simp)
  rw [applyLoop_det h.loop hloop] at h6
  exact absurd h6 (by decide)

theorem ReinitLeakIsNotCaught : Properties.ReinitLeakIsNotCaught := by
  refine ⟨fun hf => absurd (hf rowB wImpl 7 (by decide)) (by decide), valid_AB,
    swap wLeaky rowB (swap wLeaky rowA wImpl),
    ⟨code_all wLeaky (fun _ => trivial) _,
      ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide))
        (ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide)) ApplyLoop.nil), ?_⟩,
    ?_, by decide⟩
  · intro r hr; rcases mem_AB hr with rfl | rfl <;> decide
  · intro r hr; rcases mem_AB hr with rfl | rfl <;> decide

theorem ReinitMakesOrderMatter : Properties.ReinitMakesOrderMatter := by
  refine ⟨fun hf => absurd (hf rowB wImpl 7 (by decide)) (by decide), valid_AB,
    swap wOrderSensitive rowB (swap wOrderSensitive rowA wImpl),
    swap wOrderSensitive rowA (swap wOrderSensitive rowB wImpl),
    ⟨code_all wOrderSensitive (fun _ => trivial) _,
      ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide))
        (ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide)) ApplyLoop.nil), ?_⟩,
    ⟨code_all wOrderSensitive (fun _ => trivial) _,
      ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide))
        (ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide)) ApplyLoop.nil), ?_⟩,
    fun h => absurd (congrFun h 7) (by decide)⟩
  · intro r hr; rcases mem_AB hr with rfl | rfl <;> decide
  · intro r hr
    have : r = rowB ∨ r = rowA := by simpa using hr
    rcases this with rfl | rfl <;> decide

/-- The witness call, with its final state as a term. -/
lemma applyRows_AB : ApplyRows wConfig wImpl [rowA, rowB] (swap wConfig rowB (swap wConfig rowA wImpl)) := by
  refine ⟨code_all wConfig (fun _ => trivial) _,
    ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide))
      (ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide)) ApplyLoop.nil), ?_⟩
  intro r hr; rcases mem_AB hr with rfl | rfl <;> decide

theorem CurrentRowsWitness : Properties.CurrentRowsWitness := by
  have hJ := applyRows_AB
  have hK : ApplyRows wConfig wImpl [rowB, rowA] (swap wConfig rowA (swap wConfig rowB wImpl)) := by
    refine ⟨code_all wConfig (fun _ => trivial) _,
      ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide))
        (ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide)) ApplyLoop.nil), ?_⟩
    intro r hr
    have : r = rowB ∨ r = rowA := by simpa using hr
    rcases this with rfl | rfl <;> decide
  have heq := OrderIndependent wConfig wImpl _ _ [rowA, rowB] [rowB, rowA] (List.Perm.swap _ _ _)
    wConfig_frames hJ hK
  have htoRows : toRows [rowA, slotInert] = [rowA] := by decide
  have happ : RowsApplied (upd wImpl 5 11) [rowA] := by
    intro r hr; rw [List.mem_singleton.mp hr]; decide
  refine ⟨valid_AB, wConfig_frames, ?_, rfl, rfl,
    ⟨_, hJ, by rw [heq]; exact hK, by decide, by decide, by decide, trivial, rfl, hJ⟩,
    by decide, ⟨code_all wUnowned (fun _ => trivial) _, applyLoop_skip happ, happ⟩,
    by decide, by decide,
    WrongDomainTransitionReverts wConfig .core ⟨3, .ctm, [rowA, rowB]⟩ wImpl (by decide),
    htoRows, swap wConfig rowA wImpl, ?_, by decide⟩
  · intro r hr
    rcases mem_AB hr with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (fun _ => rfl)
  · rw [htoRows]
    refine ⟨code_all wConfig (fun _ => trivial) _,
      ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide)) ApplyLoop.nil, ?_⟩
    intro r hr; rw [List.mem_singleton.mp hr]; decide

end Contracts.ProxyUpgradeCurrent
