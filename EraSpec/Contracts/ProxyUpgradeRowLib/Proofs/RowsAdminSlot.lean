import EraSpec.Contracts.ProxyUpgradeRowLib.Properties.RowsAdminSlot
import EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsUnvalidated

/-!
# Proofs: the rows at `e561b9cc2`, read through the proxies' admin dispatch

Three loop lemmas carry the results that hold without `KeepsAdmin`:

* `applyLoop_frame`: under `SelfOnly`, rows naming other proxies leave both of a proxy's
  slots alone;
* `applyLoop_first`: the first row naming an administered proxy reads its implementation
  slot;
* `applyLoop_admin_change`: a proxy leaves `_admin` only in the reinitializer of a row
  naming it.

The verification field and `read_admin` then give the target slot of any proxy `_admin`
still administers.

The transfer is one step lemma, `applyRow_to_current`. Under `SelfOnly` and `KeepsAdmin`, an
iteration on an administered proxy is a `RowsCurrent` iteration on the implementation slots
and leaves the admin slots alone. Its loop forms (`applyLoop_to_current`,
`applyLoop_of_current`) give `ApplyRowsCorrespond`. The `RowsCurrent` certificates then
transfer. The countermodels and the witness are computations.
-/

namespace Contracts.ProxyUpgradeCurrent.AdminSlot

/-! ## Slots, reads and swaps -/

lemma Slots.ext' {S T : Slots} (h1 : S.impl = T.impl) (h2 : S.admin = T.admin) : S = T := by
  cases S; cases T; cases h1; cases h2; rfl

/-- Through the admin dispatch, the read is the implementation slot. -/
lemma read_admin {C : Config} {S : Slots} {p : Address} (h : S.admin p = C.proxyAdmin) :
    read C S p = some (S.impl p) := by
  unfold read; rw [ite_eq_left h]

lemma swap_frame {C : Config} (hs : SelfOnly C) {r : Row} {S : Slots} {q : Address}
    (hq : q ≠ r.proxy) : (swap C r S).impl q = S.impl q ∧ (swap C r S).admin q = S.admin q := by
  unfold swap
  split
  · obtain ⟨h1, h2⟩ := hs.1 r (S.setImpl r.proxy r.implNew) q hq
    exact ⟨h1.trans (upd_ne _ _ hq), h2⟩
  · exact ⟨upd_ne _ _ hq, rfl⟩

/-- Under `SelfOnly` and `KeepsAdmin` the reinitializer leaves every admin slot alone. -/
lemma reinit_admin {C : Config} (hs : SelfOnly C) (hk : KeepsAdmin C) (r : Row) (S : Slots) :
    (C.reinit r S).admin = S.admin := by
  funext q
  by_cases hq : q = r.proxy
  · subst hq; exact hk r S
  · exact (hs.1 r S q hq).2

/-- Under `SelfOnly` and `KeepsAdmin` a swap is the `RowsCurrent` swap on the implementation
slots. -/
lemma swap_eq {C : Config} (hs : SelfOnly C) (hk : KeepsAdmin C) (r : Row) (S : Slots) :
    swap C r S = ⟨ProxyUpgradeCurrent.swap (C.project S.admin) r S.impl, S.admin⟩ := by
  unfold swap ProxyUpgradeCurrent.swap
  by_cases hc : r.callInitializeUpgrade = true
  · rw [ite_eq_left hc, ite_eq_left hc]
    exact Slots.ext' rfl (reinit_admin hs hk r _)
  · rw [ite_eq_right hc, ite_eq_right hc]; rfl

/-! ## One row -/

lemma applyRow_frame {C : Config} (hs : SelfOnly C) {S K : Slots} {r : Row}
    (h : ApplyRow C S r K) : ∀ q, q ≠ r.proxy → K.impl q = S.impl q ∧ K.admin q = S.admin q := by
  intro q hq
  cases h with
  | alreadyAtTarget _ => exact ⟨rfl, rfl⟩
  | upgrade _ _ _ _ _ => exact swap_frame hs hq
  | upgradeForwarded _ _ _ _ _ hcall => exact hs.2 _ _ _ hcall q hq

lemma applyRow_det {C : Config} {S J K : Slots} {r : Row}
    (h₁ : ApplyRow C S r J) (h₂ : ApplyRow C S r K) : J = K := by
  cases h₁ with
  | alreadyAtTarget he =>
      cases h₂ with
      | alreadyAtTarget _ => rfl
      | upgrade _ hv hne _ _ =>
          rw [he] at hv; exact absurd (Option.some.inj hv).symm hne
      | upgradeForwarded _ hv hne _ _ _ =>
          rw [he] at hv; exact absurd (Option.some.inj hv).symm hne
  | upgrade _ hv hne _ ha =>
      cases h₂ with
      | alreadyAtTarget he =>
          rw [he] at hv; exact absurd (Option.some.inj hv).symm hne
      | upgrade _ _ _ _ _ => rfl
      | upgradeForwarded _ _ _ _ hna _ => exact absurd ha hna
  | upgradeForwarded _ hv hne _ hna hc =>
      cases h₂ with
      | alreadyAtTarget he =>
          rw [he] at hv; exact absurd (Option.some.inj hv).symm hne
      | upgrade _ _ _ _ ha => exact absurd ha hna
      | upgradeForwarded _ _ _ _ _ hc' =>
          rw [hc] at hc'; exact Option.some.inj hc'

/-- A step that takes `p` from `_admin` is a reinitializing swap of a row naming `p`. -/
lemma applyRow_admin_change {C : Config} (hs : SelfOnly C) {S K : Slots} {r : Row}
    (h : ApplyRow C S r K) {p : Address} (hS : S.admin p = C.proxyAdmin)
    (hK : K.admin p ≠ C.proxyAdmin) : r.proxy = p ∧ r.callInitializeUpgrade = true := by
  cases h with
  | alreadyAtTarget _ => exact absurd hS hK
  | upgrade _ _ _ _ _ =>
      by_cases hq : p = r.proxy
      · refine ⟨hq.symm, ?_⟩
        by_cases hc : r.callInitializeUpgrade = true
        · exact hc
        · refine absurd ?_ hK
          have hsw : (swap C r S).admin = S.admin := by
            unfold swap; rw [ite_eq_right hc]; rfl
          rw [hsw]; exact hS
      · exact absurd ((swap_frame hs hq).2.trans hS) hK
  | upgradeForwarded _ _ _ _ hna hcall =>
      by_cases hq : p = r.proxy
      · subst hq; exact absurd hS hna
      · exact absurd ((hs.2 _ _ _ hcall p hq).2.trans hS) hK

/-- Under `SelfOnly` and `KeepsAdmin`, an iteration on a proxy `_admin` administers is a
`RowsCurrent` iteration on the implementation slots, and leaves the admin slots alone. -/
lemma applyRow_to_current {C : Config} (hs : SelfOnly C) (hk : KeepsAdmin C) {S K : Slots}
    {r : Row} (h : ApplyRow C S r K) (ha : S.admin r.proxy = C.proxyAdmin) :
    K.admin = S.admin ∧ ProxyUpgradeCurrent.ApplyRow (C.project S.admin) S.impl r K.impl := by
  cases h with
  | alreadyAtTarget he =>
      rw [read_admin ha] at he
      exact ⟨rfl, ProxyUpgradeCurrent.ApplyRow.alreadyAtTarget (Option.some.inj he)⟩
  | upgrade ho hv hne hsrc _ =>
      rw [read_admin ha] at hv
      obtain rfl := Option.some.inj hv
      rw [swap_eq hs hk]
      exact ⟨rfl, ProxyUpgradeCurrent.ApplyRow.upgrade ho hne hsrc⟩
  | upgradeForwarded _ _ _ _ hna _ => exact absurd ha hna

/-! ## The loop -/

lemma applyLoop_det {C : Config} {S J K : Slots} {rows : List Row}
    (h₁ : ApplyLoop C S rows J) (h₂ : ApplyLoop C S rows K) : J = K := by
  induction h₁ generalizing K with
  | nil => cases h₂ with | nil => rfl
  | cons hstep _ ih =>
      cases h₂ with
      | cons hstep' hrest' =>
          exact ih (by rw [applyRow_det hstep hstep']; exact hrest')

/-- The loop over `xs ++ ys` runs `xs`, then `ys`. -/
lemma applyLoop_append {C : Config} {ys : List Row} :
    ∀ {xs : List Row} {S J : Slots}, ApplyLoop C S (xs ++ ys) J →
      ∃ K, ApplyLoop C S xs K ∧ ApplyLoop C K ys J
  | [], S, _, h => ⟨S, ApplyLoop.nil, h⟩
  | x :: xs, _, _, h => by
      rw [List.cons_append] at h
      cases h with
      | cons hstep hrest =>
          obtain ⟨K, h1, h2⟩ := applyLoop_append hrest
          exact ⟨K, ApplyLoop.cons hstep h1, h2⟩

/-- Under `SelfOnly`, a proxy no row names keeps both slots. -/
lemma applyLoop_frame {C : Config} (hs : SelfOnly C) {S J : Slots} {rows : List Row}
    (h : ApplyLoop C S rows J) :
    ∀ p, (∀ r ∈ rows, r.proxy ≠ p) → J.impl p = S.impl p ∧ J.admin p = S.admin p := by
  induction h with
  | nil => intro _ _; exact ⟨rfl, rfl⟩
  | @cons S K J r rs hstep _ ih =>
      intro p hp
      obtain ⟨h1, h2⟩ := ih p (fun t ht => hp t (List.mem_cons_of_mem _ ht))
      obtain ⟨h3, h4⟩ := applyRow_frame hs hstep p (fun hq => hp r List.mem_cons_self hq.symm)
      exact ⟨h1.trans h3, h2.trans h4⟩

/-- Under `SelfOnly`, the first row naming a proxy `_admin` administers finds both of its
slots where the call started, reads its implementation slot, and so finds it at the row's
target or its source. -/
lemma applyLoop_first {C : Config} (hs : SelfOnly C) {r : Row} {post : List Row} :
    ∀ {pre : List Row} {S J : Slots}, ApplyLoop C S (pre ++ r :: post) J →
      (∀ x ∈ pre, x.proxy ≠ r.proxy) → S.admin r.proxy = C.proxyAdmin →
      S.impl r.proxy = r.implNew ∨ S.impl r.proxy = r.expectedOldImpl
  | [], _, _, h, _, ha => by
      cases h with
      | cons hstep _ =>
          cases hstep with
          | alreadyAtTarget he =>
              rw [read_admin ha] at he; exact Or.inl (Option.some.inj he)
          | upgrade _ hv _ hsrc _ =>
              rw [read_admin ha] at hv; exact Or.inr ((Option.some.inj hv).trans hsrc)
          | upgradeForwarded _ _ _ _ hna _ => exact absurd ha hna
  | x :: pre, _, _, h, hpre, ha => by
      rw [List.cons_append] at h
      cases h with
      | cons hstep hrest =>
          have hfr := applyRow_frame hs hstep r.proxy
            (fun hq => hpre x List.mem_cons_self hq.symm)
          rw [← hfr.1]
          exact applyLoop_first hs hrest (fun y hy => hpre y (List.mem_cons_of_mem _ hy))
            (hfr.2.trans ha)

/-- Under `SelfOnly`, a proxy leaves `_admin` only in the reinitializer of a row naming
it. -/
lemma applyLoop_admin_change {C : Config} (hs : SelfOnly C) {S J : Slots} {rows : List Row}
    (h : ApplyLoop C S rows J) : ∀ p, S.admin p = C.proxyAdmin → J.admin p ≠ C.proxyAdmin →
      ∃ r ∈ rows, r.proxy = p ∧ r.callInitializeUpgrade = true := by
  induction h with
  | nil => intro p hS hJ; exact absurd hS hJ
  | @cons S K J r rs hstep _ ih =>
      intro p hS hJ
      by_cases hK : K.admin p = C.proxyAdmin
      · obtain ⟨t, ht, h1⟩ := ih p hK hJ
        exact ⟨t, List.mem_cons_of_mem _ ht, h1⟩
      · exact ⟨r, List.mem_cons_self, applyRow_admin_change hs hstep hS hK⟩

/-- `applyRow_to_current` for the loop. -/
lemma applyLoop_to_current {C : Config} (hs : SelfOnly C) (hk : KeepsAdmin C) {S J : Slots}
    {rows : List Row} (h : ApplyLoop C S rows J) :
    (∀ r ∈ rows, S.admin r.proxy = C.proxyAdmin) →
      J.admin = S.admin ∧ ProxyUpgradeCurrent.ApplyLoop (C.project S.admin) S.impl rows J.impl := by
  induction h with
  | nil => intro _; exact ⟨rfl, ProxyUpgradeCurrent.ApplyLoop.nil⟩
  | @cons S K J r rs hstep _ ih =>
      intro ha
      obtain ⟨hK, h0⟩ := applyRow_to_current hs hk hstep (ha r List.mem_cons_self)
      obtain ⟨hJ, h1⟩ := ih (fun t ht => by rw [hK]; exact ha t (List.mem_cons_of_mem _ ht))
      rw [hK] at h1 hJ
      exact ⟨hJ, ProxyUpgradeCurrent.ApplyLoop.cons h0 h1⟩

/-- The converse: a `RowsCurrent` loop on the implementation slots is a refined loop with the
admin slots fixed. -/
lemma applyLoop_of_current {C : Config} (hs : SelfOnly C) (hk : KeepsAdmin C)
    {A : Address → Address} {I I' : Impl} {rows : List Row}
    (h : ProxyUpgradeCurrent.ApplyLoop (C.project A) I rows I') :
    (∀ r ∈ rows, A r.proxy = C.proxyAdmin) → ApplyLoop C ⟨I, A⟩ rows ⟨I', A⟩ := by
  induction h with
  | nil => intro _; exact ApplyLoop.nil
  | @cons I J K r rs hstep _ ih =>
      intro ha
      have har : A r.proxy = C.proxyAdmin := ha r List.mem_cons_self
      have hrest := ih (fun t ht => ha t (List.mem_cons_of_mem _ ht))
      cases hstep with
      | alreadyAtTarget he =>
          refine ApplyLoop.cons (ApplyRow.alreadyAtTarget ?_) hrest
          rw [read_admin (S := ⟨I, A⟩) har]
          exact congrArg some he
      | upgrade ho hne hsrc =>
          have hstep' : ApplyRow C ⟨I, A⟩ r (swap C r ⟨I, A⟩) :=
            ApplyRow.upgrade ho (read_admin (S := ⟨I, A⟩) har) hne hsrc har
          rw [swap_eq hs hk] at hstep'
          exact ApplyLoop.cons hstep' hrest

end Contracts.ProxyUpgradeCurrent.AdminSlot

/-! ## Certificates: what holds without `KeepsAdmin` -/

namespace Contracts.ProxyUpgradeCurrent.AdminSlot

theorem AdministeredRowRunsItsTarget : Properties.AdministeredRowRunsItsTarget := by
  intro C S J rows h r hr ha
  have hv := h.verified r hr
  rw [read_admin ha] at hv
  exact Option.some.inj hv

theorem AdminLostOnlyByOwnReinitializer : Properties.AdminLostOnlyByOwnReinitializer :=
  fun _ _ _ _ p hs h hS hJ => applyLoop_admin_change hs h.loop p hS hJ

theorem OnlyNamedEdgesOrAdminLost : Properties.OnlyNamedEdgesOrAdminLost := by
  intro C S J rows hs hadm h p
  by_cases hp : ∃ r ∈ rows, r.proxy = p
  · obtain ⟨pre, r, post, rfl, rfl, hpre⟩ := exists_first_split hp
    have hr : r ∈ pre ++ r :: post := List.mem_append_right pre List.mem_cons_self
    have hstart := applyLoop_first hs h.loop hpre (hadm r hr)
    by_cases hJ : J.admin r.proxy = C.proxyAdmin
    · have hend : J.impl r.proxy = r.implNew := AdministeredRowRunsItsTarget C S J _ h r hr hJ
      have hJS : J.admin r.proxy = S.admin r.proxy := hJ.trans (hadm r hr).symm
      rcases hstart with h1 | h1
      · exact Or.inl ⟨hend.trans h1.symm, hJS⟩
      · exact Or.inr (Or.inl ⟨r, hr, rfl, h1, hend, hJS⟩)
    · obtain ⟨t, ht, htp, hti⟩ := applyLoop_admin_change hs h.loop r.proxy (hadm r hr) hJ
      exact Or.inr (Or.inr ⟨hJ, t, ht, htp, hti⟩)
  · exact Or.inl (applyLoop_frame hs h.loop p (fun r hr hq => hp ⟨r, hr, hq⟩))

theorem ReinitMovesAreCaughtOrAdminLost : Properties.ReinitMovesAreCaughtOrAdminLost := by
  intro C S J K L pre post r hd hs ha h hK hL
  obtain ⟨K', h1, h2⟩ := applyLoop_append h.loop
  rw [applyLoop_det h1 hK] at h2
  cases h2 with
  | cons hstep hrest =>
      rw [applyRow_det hstep hL] at hrest
      have hpost : ∀ x ∈ post, x.proxy ≠ r.proxy := fun x hx hq =>
        (List.pairwise_cons.mp (List.pairwise_append.mp hd).2.1).1 x hx hq.symm
      have hpre : ∀ x ∈ pre, x.proxy ≠ r.proxy := fun x hx =>
        (List.pairwise_append.mp hd).2.2 x hx r List.mem_cons_self
      have hr : r ∈ pre ++ r :: post := List.mem_append_right pre List.mem_cons_self
      obtain ⟨hJL1, hJL2⟩ := applyLoop_frame hs hrest r.proxy hpost
      obtain ⟨_, hKS2⟩ := applyLoop_frame hs hK r.proxy hpre
      by_cases hJ : J.admin r.proxy = C.proxyAdmin
      · left
        have hend := AdministeredRowRunsItsTarget C S J _ h r hr hJ
        apply Slots.ext'
        · funext q
          by_cases hq : q = r.proxy
          · subst hq
            rw [← hJL1, hend]
            exact (upd_same K.impl r.proxy r.implNew).symm
          · exact ((applyRow_frame hs hL q hq).1).trans (upd_ne K.impl r.implNew hq).symm
        · funext q
          by_cases hq : q = r.proxy
          · subst hq
            exact (hJL2.symm.trans hJ).trans ((ha r hr).symm.trans hKS2.symm)
          · exact (applyRow_frame hs hL q hq).2
      · exact Or.inr hJ

theorem SourceIsNotAppliedOnSlots : Properties.SourceIsNotAppliedOnSlots := by
  intro C S J rows r hr hne ha hs
  refine ⟨fun hread => ?_, fun h => ?_⟩
  · have hv := hread r hr
    rw [read_admin ha, hs] at hv
    exact hne (Option.some.inj hv)
  · by_cases hJ : J.admin r.proxy = C.proxyAdmin
    · refine Or.inl ⟨hJ, ?_⟩
      rw [AdministeredRowRunsItsTarget C S J rows h r hr hJ, hs]
      exact hne.symm
    · exact Or.inr hJ

end Contracts.ProxyUpgradeCurrent.AdminSlot

/-! ## Certificates: the transfer under `KeepsAdmin` -/

namespace Contracts.ProxyUpgradeCurrent.AdminSlot

theorem SelfOnlyProjectsToReinitFrames : Properties.SelfOnlyProjectsToReinitFrames :=
  fun _ A hs r I q hq => (hs.1 r ⟨I, A⟩ q hq).1

theorem RowsCurrentIsTheKeepsAdminFragment : Properties.RowsCurrentIsTheKeepsAdminFragment := by
  intro C0 a A
  refine ⟨fun _ _ => rfl,
    ⟨fun hs r I q hq => (hs.1 r ⟨I, A⟩ q hq).1,
      fun hf => ⟨fun r S q hq => ⟨hf r S.impl q hq, rfl⟩, fun r S S' h q _ => ?_⟩⟩, rfl⟩
  cases h

theorem ApplyRowsCorrespond : Properties.ApplyRowsCorrespond := by
  intro C S J rows hs hk ha
  constructor
  · intro h
    obtain ⟨hJ, h0⟩ := applyLoop_to_current hs hk h.loop ha
    refine ⟨⟨h.code, h0, fun r hr => ?_⟩, hJ⟩
    have hv := h.verified r hr
    rw [read_admin (show J.admin r.proxy = C.proxyAdmin by rw [hJ]; exact ha r hr)] at hv
    exact Option.some.inj hv
  · rintro ⟨h0, hJ⟩
    have hloop := applyLoop_of_current hs hk h0.loop ha
    have hJ' : (⟨J.impl, S.admin⟩ : Slots) = J := Slots.ext' rfl hJ.symm
    rw [hJ'] at hloop
    refine ⟨h0.code, hloop, fun r hr => ?_⟩
    rw [read_admin (show J.admin r.proxy = C.proxyAdmin by rw [hJ]; exact ha r hr)]
    exact congrArg some (h0.verified r hr)

theorem ApplyRowsPostconditionOnSlots : Properties.ApplyRowsPostconditionOnSlots := by
  intro C S J rows hs hk ha h r hr
  obtain ⟨h0, hJ⟩ := (ApplyRowsCorrespond C S J rows hs hk ha).mp h
  exact ⟨h0.verified r hr, by rw [hJ]; exact ha r hr⟩

theorem OnlyNamedEdgesAcrossCallOnSlots : Properties.OnlyNamedEdgesAcrossCallOnSlots := by
  intro C S J rows hs hk ha h
  obtain ⟨h0, hJ⟩ := (ApplyRowsCorrespond C S J rows hs hk ha).mp h
  exact ⟨hJ, ProxyUpgradeCurrent.OnlyNamedEdgesAcrossCallAnyRows _ _ _ _
    (SelfOnlyProjectsToReinitFrames C S.admin hs) h0⟩

theorem OnlyNamedEdgesAcrossTransitionOnSlots :
    Properties.OnlyNamedEdgesAcrossTransitionOnSlots :=
  fun C _ T S J hs hk ha h => OnlyNamedEdgesAcrossCallOnSlots C S J T.rows hs hk ha h.2.2

theorem ReinitMovesAreCaughtOnLastRowOnSlots :
    Properties.ReinitMovesAreCaughtOnLastRowOnSlots := by
  intro C S J K L pre post r hs hk ha h hK hL hpost
  obtain ⟨h0, _⟩ := (ApplyRowsCorrespond C S J _ hs hk ha).mp h
  obtain ⟨hKA, hK0⟩ :=
    applyLoop_to_current hs hk hK (fun t ht => ha t (List.mem_append_left _ ht))
  have hr : K.admin r.proxy = C.proxyAdmin := by
    rw [hKA]; exact ha r (List.mem_append_right pre List.mem_cons_self)
  obtain ⟨hLA, hL0⟩ := applyRow_to_current hs hk hL hr
  rw [hKA] at hL0
  exact Slots.ext' (ProxyUpgradeCurrent.ReinitMovesAreCaughtOnLastRow _ _ _ _ _ pre post r
    (SelfOnlyProjectsToReinitFrames C S.admin hs) h0 hK0 hL0 hpost) hLA

theorem ReinitMovesAreCaughtOnDistinctRowsOnSlots :
    Properties.ReinitMovesAreCaughtOnDistinctRowsOnSlots :=
  fun C S J K L pre post r hd hs hk ha h hK hL =>
    ReinitMovesAreCaughtOnLastRowOnSlots C S J K L pre post r hs hk ha h hK hL fun x hx hq =>
      (List.pairwise_cons.mp (List.pairwise_append.mp hd).2.1).1 x hx hq.symm

theorem OrderIndependentOnSlots : Properties.OrderIndependentOnSlots := by
  intro C S J K rows rows' hperm hs hk ha h h'
  have ha' : Administered C S rows' := fun r hr => ha r (hperm.mem_iff.mpr hr)
  obtain ⟨h0, hJ⟩ := (ApplyRowsCorrespond C S J rows hs hk ha).mp h
  obtain ⟨h0', hK⟩ := (ApplyRowsCorrespond C S K rows' hs hk ha').mp h'
  exact Slots.ext' (ProxyUpgradeCurrent.OrderIndependent _ _ _ _ rows rows' hperm
    (SelfOnlyProjectsToReinitFrames C S.admin hs) h0 h0') (hJ.trans hK.symm)

end Contracts.ProxyUpgradeCurrent.AdminSlot

/-! ## Countermodels and the witness -/

namespace Contracts.ProxyUpgradeCurrent.AdminSlot

lemma wCfg_selfOnly : SelfOnly wCfg :=
  ((RowsCurrentIsTheKeepsAdminFragment wConfig wAdmin wSlots.admin).2.1).mpr wConfig_frames

lemma wCfg_keeps : KeepsAdmin wCfg :=
  (RowsCurrentIsTheKeepsAdminFragment wConfig wAdmin wSlots.admin).1

/-- A reinitializer of the form `if r = rowB then (S.setAdmin 6 x).setImpl 6 (f S) else S`
writes only proxy `6`, `rowB`'s proxy. -/
lemma rowB_rewrite_frame (x : Address) (f : Slots → Address) (r : Row) (S : Slots) (q : Address)
    (hq : q ≠ r.proxy) :
    ((if r = rowB then (S.setAdmin 6 x).setImpl 6 (f S) else S : Slots)).impl q = S.impl q ∧
      ((if r = rowB then (S.setAdmin 6 x).setImpl 6 (f S) else S : Slots)).admin q = S.admin q := by
  split_ifs with h
  · subst h
    have hq6 : q ≠ 6 := hq
    exact ⟨upd_ne _ _ hq6, upd_ne _ _ hq6⟩
  · exact ⟨rfl, rfl⟩

lemma adminRewrite_selfOnly : SelfOnly wAdminRewrite :=
  ⟨fun r S q hq => rowB_rewrite_frame 66 (fun _ => 99) r S q hq, fun _ _ _ h => by cases h⟩

lemma adminRewriteOrder_selfOnly : SelfOnly wAdminRewriteOrder :=
  ⟨fun r S q hq => rowB_rewrite_frame 66 (fun S => if S.impl 5 = 11 then 98 else 99) r S q hq,
    fun _ _ _ h => by cases h⟩

lemma adminRewriteBack_selfOnly : SelfOnly wAdminRewriteBack :=
  ⟨fun r S q hq => rowB_rewrite_frame 66 (fun _ => 10) r S q hq, fun _ _ _ h => by cases h⟩

/-- `rowA` then `rowB` under the admin-rewriting reinitializer. -/
lemma adminRewrite_rows :
    ApplyRows wAdminRewrite wSlots [rowA, rowB]
      (swap wAdminRewrite rowB (swap wAdminRewrite rowA wSlots)) := by
  refine ⟨fun _ _ => trivial,
    ApplyLoop.cons (ApplyRow.upgrade (v := 10) rfl (by decide) (by decide) (by decide) (by decide))
      (ApplyLoop.cons
        (ApplyRow.upgrade (v := 10) rfl (by decide) (by decide) (by decide) (by decide))
        ApplyLoop.nil), ?_⟩
  intro r hr; rcases mem_pair hr with rfl | rfl <;> decide

/-- `RowsCurrent` reverts the same call: its verification sees proxy `6` at `99`. -/
lemma adminRewrite_current_reverts :
    ¬ ∃ I, ProxyUpgradeCurrent.ApplyRows (wAdminRewrite.project wSlots.admin) wSlots.impl
      [rowA, rowB] I := by
  rintro ⟨I, h⟩
  have hloop : ProxyUpgradeCurrent.ApplyLoop (wAdminRewrite.project wSlots.admin) wSlots.impl
      [rowA, rowB]
      (ProxyUpgradeCurrent.swap (wAdminRewrite.project wSlots.admin) rowB
        (ProxyUpgradeCurrent.swap (wAdminRewrite.project wSlots.admin) rowA wSlots.impl)) :=
    ProxyUpgradeCurrent.ApplyLoop.cons
      (ProxyUpgradeCurrent.ApplyRow.upgrade rfl (by decide) (by decide))
      (ProxyUpgradeCurrent.ApplyLoop.cons
        (ProxyUpgradeCurrent.ApplyRow.upgrade rfl (by decide) (by decide))
        ProxyUpgradeCurrent.ApplyLoop.nil)
  have h6 := h.verified rowB (by simp)
  rw [ProxyUpgradeCurrent.applyLoop_det h.loop hloop] at h6
  exact absurd h6 (by decide)

theorem AdminRewriteDefeatsVerification : Properties.AdminRewriteDefeatsVerification := by
  refine ⟨adminRewrite_selfOnly, SelfOnlyProjectsToReinitFrames _ _ adminRewrite_selfOnly,
    fun hk => absurd (hk rowB wSlots) (by decide), valid_AB, fun _ _ => rfl,
    adminRewrite_current_reverts, _, adminRewrite_rows, ⟨trivial, rfl, adminRewrite_rows⟩,
    adminRewrite_rows.verified rowB (by simp), by decide, by decide, ?_,
    swap wAdminRewrite rowA wSlots, _,
    ApplyLoop.cons
      (ApplyRow.upgrade (v := 10) rfl (by decide) (by decide) (by decide) (by decide))
      ApplyLoop.nil,
    ApplyRow.upgrade (v := 10) rfl (by decide) (by decide) (by decide) (by decide), ?_⟩
  · rintro (h | ⟨r, hr, hp, _, himpl⟩)
    · exact absurd h (by decide)
    · rcases mem_pair hr with rfl | rfl
      · exact absurd hp (by decide)
      · exact absurd himpl (by decide)
  · intro h
    exact absurd (congrArg (fun S => S.impl 6) h) (by decide)

theorem AdminRewriteMakesOrderMatter : Properties.AdminRewriteMakesOrderMatter := by
  have hJ : ApplyRows wAdminRewriteOrder wSlots [rowA, rowB]
      (swap wAdminRewriteOrder rowB (swap wAdminRewriteOrder rowA wSlots)) := by
    refine ⟨fun _ _ => trivial,
      ApplyLoop.cons
        (ApplyRow.upgrade (v := 10) rfl (by decide) (by decide) (by decide) (by decide))
        (ApplyLoop.cons
          (ApplyRow.upgrade (v := 10) rfl (by decide) (by decide) (by decide) (by decide))
          ApplyLoop.nil), ?_⟩
    intro r hr; rcases mem_pair hr with rfl | rfl <;> decide
  have hK : ApplyRows wAdminRewriteOrder wSlots [rowB, rowA]
      (swap wAdminRewriteOrder rowA (swap wAdminRewriteOrder rowB wSlots)) := by
    refine ⟨fun _ _ => trivial,
      ApplyLoop.cons
        (ApplyRow.upgrade (v := 10) rfl (by decide) (by decide) (by decide) (by decide))
        (ApplyLoop.cons
          (ApplyRow.upgrade (v := 10) rfl (by decide) (by decide) (by decide) (by decide))
          ApplyLoop.nil), ?_⟩
    intro r hr; rcases mem_pair hr with rfl | rfl <;> decide
  exact ⟨adminRewriteOrder_selfOnly,
    SelfOnlyProjectsToReinitFrames _ _ adminRewriteOrder_selfOnly, valid_AB, fun _ _ => rfl,
    _, _, hJ, hK, by simp, by decide⟩

/-- On the implementation mapping, `wAdminRewriteBack` is `wSelfMoving`. -/
lemma adminRewriteBack_project : wAdminRewriteBack.project wSlots.admin = wSelfMoving := by
  simp only [Config.project, wAdminRewriteBack, wSelfMoving, wCfg, lift, wConfig]
  congr 1
  funext r I
  split_ifs <;> rfl

theorem MoveBackWithAdminRewriteIsNotCaught : Properties.MoveBackWithAdminRewriteIsNotCaught := by
  have hJ : ApplyRows wAdminRewriteBack wSlots [rowA, rowB]
      (swap wAdminRewriteBack rowB (swap wAdminRewriteBack rowA wSlots)) := by
    refine ⟨fun _ _ => trivial,
      ApplyLoop.cons
        (ApplyRow.upgrade (v := 10) rfl (by decide) (by decide) (by decide) (by decide))
        (ApplyLoop.cons
          (ApplyRow.upgrade (v := 10) rfl (by decide) (by decide) (by decide) (by decide))
          ApplyLoop.nil), ?_⟩
    intro r hr; rcases mem_pair hr with rfl | rfl <;> decide
  exact ⟨adminRewriteBack_selfOnly, adminRewriteBack_project, valid_AB, fun _ _ => rfl,
    ProxyUpgradeCurrent.ReinitMovingOwnProxyIsCaught.2.2.2, rfl, _, hJ, by decide, by decide⟩

theorem UnadministeredProxyFoolsTheSkip : Properties.UnadministeredProxyFoolsTheSkip := by
  refine ⟨wCfg_selfOnly, wCfg_keeps, valid_B, fun ha => absurd (ha rowB (by simp)) (by decide),
    ⟨fun _ _ => trivial, ApplyLoop.cons (ApplyRow.alreadyAtTarget (by decide)) ApplyLoop.nil,
      ?_⟩, by decide⟩
  intro r hr; rw [List.mem_singleton.mp hr]; decide

theorem AdminSlotWitness : Properties.AdminSlotWitness := by
  have hs' : SelfOnly wKeepAdminSelfMoving :=
    ((RowsCurrentIsTheKeepsAdminFragment wSelfMoving wAdmin wSlots.admin).2.1).mpr
      selfMoving_frames
  have hk' : KeepsAdmin wKeepAdminSelfMoving :=
    (RowsCurrentIsTheKeepsAdminFragment wSelfMoving wAdmin wSlots.admin).1
  have hJ : ApplyRows wCfg wSlots [rowA, rowB] (swap wCfg rowB (swap wCfg rowA wSlots)) := by
    refine ⟨fun _ _ => trivial,
      ApplyLoop.cons
        (ApplyRow.upgrade (v := 10) rfl (by decide) (by decide) (by decide) (by decide))
        (ApplyLoop.cons
          (ApplyRow.upgrade (v := 10) rfl (by decide) (by decide) (by decide) (by decide))
          ApplyLoop.nil), ?_⟩
    intro r hr; rcases mem_pair hr with rfl | rfl <;> decide
  refine ⟨wCfg_selfOnly, wCfg_keeps, fun _ _ => rfl, valid_AB,
    ⟨_, hJ, by decide, by decide, rfl⟩, hs', hk', fun _ _ => rfl,
    ⟨_, ApplyLoop.cons
        (ApplyRow.upgrade (v := 10) rfl (by decide) (by decide) (by decide) (by decide))
        (ApplyLoop.cons
          (ApplyRow.upgrade (v := 10) rfl (by decide) (by decide) (by decide) (by decide))
          ApplyLoop.nil)⟩, ?_⟩
  rintro ⟨J, h⟩
  obtain ⟨h0, _⟩ := (ApplyRowsCorrespond _ _ _ _ hs' hk' (fun _ _ => rfl)).mp h
  exact ProxyUpgradeCurrent.ReinitMovingOwnProxyIsCaught.2.2.2 ⟨J.impl, h0⟩

end Contracts.ProxyUpgradeCurrent.AdminSlot
