import EraSpec.Contracts.ChainAssetHandler.Properties.Migration

/-!
# Proofs: where a chain settles, its migration number, and recovery

The reachability results are inductive invariants over `Reach`, proved in layers: message
ids are fresh (`fresh_inv`); L1's bookkeeping (`book_inv`); bridgehub/diamond agreement
(`agree_inv`); the holder invariant (`hold_inv`), which uses freshness; and the L1-message
invariant behind `isMigrationInProgress` (`l1msg_inv`), which uses freshness. Each layer is
proved by `reach_induction`, case by case over the steps.
-/

namespace Contracts.ChainAssetHandler

/-! ## Generic -/

@[simp] theorem upd_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) :
    upd f a b a = b := by simp [upd]

theorem upd_ne {α β : Type} [DecidableEq α] (f : α → β) {a x : α} (b : β) (h : x ≠ a) :
    upd f a b x = f x := by simp [upd, h]

theorem upd2_apply {α β γ : Type} [DecidableEq α] [DecidableEq β] (f : α → β → γ) (a : α)
    (b : β) (v : γ) (x : α) (y : β) :
    upd2 f a b v x y = if x = a ∧ y = b then v else f x y := rfl

/-- Induction over reachable states. -/
theorem reach_induction {W : World} (P : Sys → Prop)
    (h0 : ∀ s, Init s → P s)
    (hs : ∀ s l s', Reach W s → P s → Step W s l s' → P s') :
    ∀ s, Reach W s → P s := by
  intro s hr
  induction hr with
  | init hi => exact h0 _ hi
  | step hr hst ih => exact hs _ _ _ hr ih hst

/-- A run from a reachable state ends in a reachable state. -/
theorem Run.reach {W : World} {s s' : Sys} {ls : List Label} (h : Run W s ls s') :
    Reach W s → Reach W s' := by
  induction h with
  | nil => exact id
  | cons hst _ ih => exact fun hr => ih (Reach.step hr hst)

/-! ## Layer 0: message ids are fresh -/

theorem fresh_inv {W : World} : ∀ s, Reach W s → ∀ i, s.nMsgs ≤ i → s.msgs i = none := by
  refine reach_induction _ (fun s hi i _ => hi.msgs i) ?_
  intro s l s' _ ih hst
  cases hst with
  | burn =>
    intro i hi
    simp only [burnPost] at hi ⊢
    rw [upd_ne _ _ (by omega)]
    exact ih i (by omega)
  | @mintFresh _ j m hm =>
    intro i hi
    simp only [mintPost] at hi ⊢
    have hj : j ≠ i := fun h => by subst h; simp [ih j hi] at hm
    rw [upd_ne _ _ (Ne.symm hj)]; exact ih i hi
  | @mintReturn _ j m hm =>
    intro i hi
    simp only [mintPost] at hi ⊢
    have hj : j ≠ i := fun h => by subst h; simp [ih j hi] at hm
    rw [upd_ne _ _ (Ne.symm hj)]; exact ih i hi
  | @failDeposit j m hm =>
    intro i hi
    have hj : j ≠ i := fun h => by subst h; simp [ih j hi] at hm
    simp only at hi ⊢
    rw [upd_ne _ _ (Ne.symm hj)]; exact ih i hi
  | @confirm j m f hm =>
    intro i hi
    have hi' : s.nMsgs ≤ i := by cases f <;> exact hi
    have hj : i ≠ j := fun h => by subst h; simp [ih i hi'] at hm
    cases f <;> simp [confirmPost, upd, hj, ih i hi']
  | register => exact ih
  | pauseMigration => exact ih
  | unpauseMigration => exact ih
  | pauseCTM => exact ih
  | unpauseCTM => exact ih
  | pause => exact ih
  | unpause => exact ih
  | ctmUpgrade => exact ih
  | diamondUpgrade => exact ih

/-! ## Layer 1: L1 bookkeeping -/

/-- L1's bookkeeping for chain `c` (the inductive part of `L1MigrationBookkeeping`). -/
def Book (W : World) (s : Sys) (c : ChainId) : Prop :=
  s.migNum W.l1 c ≤ maxMigrations ∧
  (s.reg W.l1 c = false → s.migNum W.l1 c = 0) ∧
  (s.migNum W.l1 c = 0 → s.ivActive c = false ∧ s.ivSL c = 0) ∧
  (s.migNum W.l1 c = 0 → s.reg W.l1 c = true → s.sl W.l1 c = W.l1) ∧
  (s.migNum W.l1 c = numToSL →
    s.ivActive c = true ∧ s.ivSL c = s.sl W.l1 c ∧ s.sl W.l1 c ≠ W.l1) ∧
  (s.migNum W.l1 c = numToL1 → s.ivActive c = false ∧ s.sl W.l1 c = W.l1)

theorem Book.congr {W : World} {s s' : Sys} {c : ChainId} (hb : Book W s c)
    (h1 : s'.migNum W.l1 c = s.migNum W.l1 c) (h2 : s'.reg W.l1 c = s.reg W.l1 c)
    (h3 : s'.ivActive c = s.ivActive c) (h4 : s'.ivSL c = s.ivSL c)
    (h5 : s'.sl W.l1 c = s.sl W.l1 c) : Book W s' c := by
  unfold Book; rw [h1, h2, h3, h4, h5]; exact hb

theorem book_zero {W : World} {s : Sys} {c : ChainId} (hm : s.migNum W.l1 c = 0)
    (ha : s.ivActive c = false) (hs : s.ivSL c = 0)
    (hsl : s.reg W.l1 c = true → s.sl W.l1 c = W.l1) : Book W s c := by
  simp [Book, hm, ha, hs, numToSL, numToL1, maxMigrations]; exact hsl

theorem book_one {W : World} {s : Sys} {c : ChainId} (hm : s.migNum W.l1 c = numToSL)
    (hr : s.reg W.l1 c = true) (ha : s.ivActive c = true) (hs : s.ivSL c = s.sl W.l1 c)
    (hne : s.sl W.l1 c ≠ W.l1) : Book W s c := by
  simp [Book, hm, hr, ha, hs, hne, numToSL, numToL1, maxMigrations]

theorem book_two {W : World} {s : Sys} {c : ChainId} (hm : s.migNum W.l1 c = numToL1)
    (hr : s.reg W.l1 c = true) (ha : s.ivActive c = false) (hsl : s.sl W.l1 c = W.l1) :
    Book W s c := by
  simp [Book, hm, hr, ha, hsl, numToSL, numToL1, maxMigrations]

theorem book_inv {W : World} : ∀ s, Reach W s → ∀ c, Book W s c := by
  refine reach_induction _ (fun s hi c => ?_) ?_
  · exact book_zero (hi.migNum _ _) (hi.ivActive _) (hi.ivSL _) (by simp [hi.reg])
  intro s l s' _ ih hst c
  have hb := ih c
  obtain ⟨_, h2, h3, _, _, _⟩ := id hb
  cases hst with
  | @register c0 x _ _ _ _ hnr =>
    by_cases hc : c = c0
    · subst hc
      have h0 := h2 hnr
      exact book_zero (by simpa [registerPost, upd2_apply] using h0) (h3 h0).1 (h3 h0).2
        (fun _ => by simp [registerPost, upd2_apply])
    · exact hb.congr (by simp [registerPost]) (by simp [registerPost, upd2_apply, hc])
        rfl rfl (by simp [registerPost, upd2_apply, hc])
  | @burn h c0 t a o hh0 _ _ _ _ _ _ _ hsl _ hreg _ _ _ hnl _ _ _ hl1 =>
    by_cases hh : h = W.l1
    · subst hh
      obtain ⟨htl, hn⟩ := hl1 rfl
      by_cases hc : c = c0
      · subst hc
        exact book_one (by simp [burnPost, upd2_apply, hn]) (by simpa [burnPost] using hreg)
          (by simp [burnPost]) (by simp [burnPost, upd2_apply])
          (by simpa [burnPost, upd2_apply] using htl)
      · exact hb.congr (by simp [burnPost, upd2_apply, hc]) rfl
          (by simp [burnPost, upd, hc]) (by simp [burnPost, upd, hc])
          (by simp [burnPost, upd2_apply, hc])
    · have hh' : W.l1 ≠ h := Ne.symm hh
      exact hb.congr (by simp [burnPost, upd2_apply, hh']) rfl (by simp [burnPost, hh])
        (by simp [burnPost, hh]) (by simp [burnPost, upd2_apply, hh'])
  | @mintFresh h i m _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnl =>
    have hh : W.l1 ≠ h := Ne.symm hnl
    exact hb.congr (by simp [mintPost, upd2_apply, hh]) (by simp [mintPost, upd2_apply, hh])
      (by simp [mintPost, hnl]) rfl (by simp [mintPost, upd2_apply, hh])
  | @mintReturn h i m _ _ _ _ _ _ _ _ hl1 hiv _ _ hreg _ _ =>
    by_cases hh : h = W.l1
    · subst hh
      obtain ⟨_, hmn⟩ := hl1 rfl
      by_cases hc : c = m.chain
      · subst hc
        exact book_two (by simp [mintPost, upd2_apply, hmn]) (by simp [mintPost, upd2_apply])
          (by simp [mintPost]) (by simp [mintPost, upd2_apply])
      · exact hb.congr (by simp [mintPost, upd2_apply, hc]) (by simp [mintPost, upd2_apply, hc])
          (by simp [mintPost, upd, hc]) rfl (by simp [mintPost, upd2_apply, hc])
    · have hh' : W.l1 ≠ h := Ne.symm hh
      exact hb.congr (by simp [mintPost, upd2_apply, hh']) (by simp [mintPost, upd2_apply, hh'])
        (by simp [mintPost, hh]) rfl (by simp [mintPost, upd2_apply, hh'])
  | failDeposit => exact hb
  | @confirm i m f _ _ hfail _ hreg _ hnum _ _ =>
    cases f
    · exact hb.congr rfl rfl rfl rfl rfl
    · have hn := hnum rfl
      by_cases hc : c = m.chain
      · subst hc
        exact book_zero (by simp [confirmPost, upd2_apply, hn, numToSL]) (by simp [confirmPost])
          (by simp [confirmPost]) (fun _ => by simp [confirmPost, upd2_apply])
      · exact hb.congr (by simp [confirmPost, upd2_apply, hc]) rfl
          (by simp [confirmPost, upd, hc]) (by simp [confirmPost, upd, hc])
          (by simp [confirmPost, upd2_apply, hc])
  | pauseMigration => exact hb
  | unpauseMigration => exact hb
  | pauseCTM => exact hb
  | unpauseCTM => exact hb
  | pause => exact hb
  | unpause => exact hb
  | ctmUpgrade => exact hb
  | diamondUpgrade => exact hb

/-! ## Layer 2: the bridgehub and the diamond agree -/

theorem agree_inv {W : World} (hl : W.l1 ≠ 0) : ∀ s, Reach W s → ∀ h c, s.reg h c = true →
    h ≠ 0 ∧ (s.sl h c = h ↔ s.away h c = false) := by
  refine reach_induction _ (fun s hi h c hr => by simp [hi.reg] at hr) ?_
  intro s l s' _ ih hst hq cq hr
  cases hst with
  | @register c0 x _ _ _ _ _ =>
    by_cases hp : hq = W.l1 ∧ cq = c0
    · obtain ⟨rfl, rfl⟩ := hp
      simp [registerPost, upd2_apply, hl]
    · simp only [registerPost, upd2_apply, hp, ite_false] at hr ⊢
      exact ih hq cq hr
  | @burn h c0 t a o hh0 _ _ _ _ _ _ _ _ _ _ _ _ _ hnl _ _ _ hl1 =>
    by_cases hp : hq = h ∧ cq = c0
    · obtain ⟨rfl, rfl⟩ := hp
      have htne : t ≠ hq := by
        by_cases hh : hq = W.l1
        · exact hh ▸ (hl1 hh).1
        · rw [hnl hh]; exact Ne.symm hh
      simp [burnPost, upd2_apply, hh0, htne]
    · simp only [burnPost, upd2_apply, hp, ite_false] at hr ⊢
      exact ih hq cq hr
  | @mintFresh h i m _ _ _ hh0 =>
    by_cases hp : hq = h ∧ cq = m.chain
    · obtain ⟨rfl, rfl⟩ := hp
      simp [mintPost, upd2_apply, hh0]
    · simp only [mintPost, upd2_apply, hp, ite_false] at hr ⊢
      exact ih hq cq hr
  | @mintReturn h i m _ _ _ hh0 =>
    by_cases hp : hq = h ∧ cq = m.chain
    · obtain ⟨rfl, rfl⟩ := hp
      simp [mintPost, upd2_apply, hh0]
    · simp only [mintPost, upd2_apply, hp, ite_false] at hr ⊢
      exact ih hq cq hr
  | failDeposit => exact ih hq cq hr
  | @confirm i m f =>
    cases f
    · exact ih hq cq hr
    · by_cases hp : hq = W.l1 ∧ cq = m.chain
      · obtain ⟨rfl, rfl⟩ := hp
        simp [confirmPost, upd2_apply, hl]
      · simp only [confirmPost, upd2_apply, hp, ite_false, ite_true] at hr ⊢
        exact ih hq cq hr
  | pauseMigration => exact ih hq cq hr
  | unpauseMigration => exact ih hq cq hr
  | pauseCTM => exact ih hq cq hr
  | unpauseCTM => exact ih hq cq hr
  | pause => exact ih hq cq hr
  | unpause => exact ih hq cq hr
  | ctmUpgrade => exact ih hq cq hr
  | diamondUpgrade => exact ih hq cq hr

/-! ## Layer 3: one holder per chain -/

/-- The holder invariant for chain `c`. -/
def HoldInv (W : World) (s : Sys) (c : ChainId) : Prop :=
  (s.reg W.l1 c = true → ∃ x, ∀ y, Holds s c y ↔ y = x) ∧
  (s.reg W.l1 c = false → ∀ y, ¬ Holds s c y)

theorem HoldInv.congr {W : World} {s s' : Sys} {c : ChainId} (hi : HoldInv W s c)
    (hr : s'.reg W.l1 c = s.reg W.l1 c) (hh : ∀ y, Holds s' c y ↔ Holds s c y) :
    HoldInv W s' c := by
  refine ⟨fun h => ?_, fun h y => ?_⟩
  · obtain ⟨x, hx⟩ := hi.1 (hr ▸ h); exact ⟨x, fun y => (hh y).trans (hx y)⟩
  · rw [hh]; exact hi.2 (hr ▸ h) y

/-- The holder of a registered chain is its unique holder. -/
theorem HoldInv.unique {W : World} {s : Sys} {c : ChainId} (hi : HoldInv W s c) {x : Holder}
    (hx : Holds s c x) : ∀ y, Holds s c y ↔ y = x := by
  by_cases hr : s.reg W.l1 c = true
  · obtain ⟨x0, h0⟩ := hi.1 hr
    have := (h0 x).1 hx; subst this; exact h0
  · exact absurd hx (hi.2 (by simpa using hr) x)

theorem HoldInv.reg {W : World} {s : Sys} {c : ChainId} (hi : HoldInv W s c) {x : Holder}
    (hx : Holds s c x) : s.reg W.l1 c = true := by
  by_contra hr; exact hi.2 (by simpa using hr) x hx

/-- Holds is determined by the settlement-layer records and the live messages of a chain. -/
theorem holds_congr {s s' : Sys} {c : ChainId} (hsl : ∀ h, s'.sl h c = s.sl h c)
    (hm : ∀ j, (∃ m, s'.msgs j = some m ∧ m.chain = c ∧ m.Live) ↔
      (∃ m, s.msgs j = some m ∧ m.chain = c ∧ m.Live)) :
    ∀ y, Holds s' c y ↔ Holds s c y := by
  intro y; cases y with
  | hub h => simp only [Holds, hsl]
  | msg j => exact hm j

/-- A mint moves its chain from the message to the minting hub. -/
theorem hold_mint {W : World} {s : Sys} {h : ChainId} {i : ℕ} {m : Msg} {x : Address}
    {fresh : Bool} (hl : W.l1 ≠ 0)
    (ihm : ∀ i m, s.msgs i = some m → s.reg W.l1 m.chain = true) (ih : ∀ c, HoldInv W s c)
    (hm : s.msgs i = some m) (hpend : m.status = .pending) (hh0 : h ≠ 0) :
    (∀ j m', (mintPost W s h i m x fresh).msgs j = some m' →
        (mintPost W s h i m x fresh).reg W.l1 m'.chain = true) ∧
      ∀ c, HoldInv W (mintPost W s h i m x fresh) c := by
  have hmsg : Holds s m.chain (.msg i) := ⟨m, hm, rfl, Or.inl hpend⟩
  have hregc := (ih m.chain).reg hmsg
  refine ⟨fun j m' hm' => ?_, fun cq => ?_⟩
  · simp only [mintPost, upd] at hm' ⊢
    split_ifs at hm' with hj
    · cases hm'; simp [upd2_apply, hregc]
    · have := ihm j m' hm'; simp [upd2_apply, this]
  · by_cases hc : cq = m.chain
    · subst hc
      have hu := (ih m.chain).unique hmsg
      refine ⟨fun _ => ⟨.hub h, fun y => ?_⟩, fun hr => by
        simp [mintPost, upd2_apply, hregc] at hr⟩
      cases y with
      | hub h' =>
        simp only [Holds, mintPost, upd2_apply]
        by_cases hh : h' = h
        · subst hh; simp [hh0]
        · have := hu (.hub h'); simp only [Holds] at this
          simp [hh, this]
      | msg j =>
        simp only [Holds, mintPost, upd]
        by_cases hj : j = i
        · subst hj; simp [Msg.Live]
        · have := hu (.msg j); simp only [Holds] at this
          simp [hj, this]
    · have hreg' : (mintPost W s h i m x fresh).reg W.l1 cq = s.reg W.l1 cq := by
        simp [mintPost, upd2_apply, hc]
      refine (ih cq).congr hreg' (holds_congr (fun h' => by simp [mintPost, upd2_apply, hc])
        (fun j => ?_))
      simp only [mintPost, upd]
      split_ifs with hj
      · subst hj; simp [hm, Ne.symm hc]
      · exact Iff.rfl

theorem hold_inv {W : World} (hl : W.l1 ≠ 0) : ∀ s, Reach W s →
    (∀ i m, s.msgs i = some m → s.reg W.l1 m.chain = true) ∧ ∀ c, HoldInv W s c := by
  refine reach_induction _ (fun s hi => ⟨fun i m h => by simp [hi.msgs] at h,
    fun c => ⟨fun h => by simp [hi.reg] at h, fun _ y => ?_⟩⟩) ?_
  · cases y with
    | hub h => simp only [Holds, hi.sl]; exact fun ⟨h1, h2⟩ => h1 h2.symm
    | msg j => simp [Holds, hi.msgs]
  intro s l s' hreach ⟨ihm, ih⟩ hst
  cases hst with
  | @register c0 x _ _ _ _ hnr =>
    refine ⟨fun i m hm => ?_, fun cq => ?_⟩
    · have := ihm i m hm
      simp only [registerPost, upd2_apply]; split_ifs <;> simp_all
    · by_cases hc : cq = c0
      · subst hc
        refine ⟨fun _ => ⟨.hub W.l1, fun y => ?_⟩, fun h => by simp [registerPost, upd2_apply] at h⟩
        have hno := (ih cq).2 hnr
        cases y with
        | hub h' =>
          by_cases hh : h' = W.l1
          · subst hh; simp [Holds, registerPost, upd2_apply, hl]
          · have := hno (.hub h')
            simp only [Holds, registerPost, upd2_apply, hh, false_and, ite_false] at this ⊢
            simp [this, hh]
        | msg j => have := hno (.msg j); simpa [Holds, registerPost] using this
      · refine (ih cq).congr (by simp [registerPost, upd2_apply, hc]) ?_
        exact holds_congr (fun h => by simp [registerPost, upd2_apply, hc]) (fun j => Iff.rfl)
  | @burn h c0 t a o hh0 _ _ _ _ _ _ _ hsl _ _ _ _ _ hnl _ _ _ hl1 =>
    have hfresh := fresh_inv s hreach s.nMsgs le_rfl
    have hhub : Holds s c0 (.hub h) := ⟨hh0, hsl⟩
    have hregc := (ih c0).reg hhub
    have htne : t ≠ h := by
      by_cases hh : h = W.l1
      · exact hh ▸ (hl1 hh).1
      · rw [hnl hh]; exact Ne.symm hh
    refine ⟨fun i m hm => ?_, fun cq => ?_⟩
    · simp only [burnPost, upd] at hm ⊢
      split_ifs at hm with hi
      · cases hm; exact hregc
      · exact ihm i m hm
    · by_cases hc : cq = c0
      · subst hc
        have hu := (ih cq).unique hhub
        refine ⟨fun _ => ⟨.msg s.nMsgs, fun y => ?_⟩, fun h => by simp [burnPost, hregc] at h⟩
        cases y with
        | hub h' =>
          simp only [Holds, burnPost, upd2_apply]
          by_cases hh : h' = h
          · subst hh; simp [htne]
          · have := hu (.hub h'); simp only [Holds] at this
            simp [hh, this]
        | msg j =>
          by_cases hj : j = s.nMsgs
          · subst hj; simp [Holds, burnPost, burnMsg, Msg.Live]
          · have := hu (.msg j); simp only [Holds] at this
            simp only [Holds, burnPost, upd, hj, ite_false, this]; simp [hj]
      · refine (ih cq).congr rfl ?_
        refine holds_congr (fun h' => by simp [burnPost, upd2_apply, hc]) (fun j => ?_)
        simp only [burnPost, upd]
        split_ifs with hj
        · subst hj; simp [hfresh, burnMsg, Ne.symm hc]
        · exact Iff.rfl
  | @mintFresh h i m hm hpend _ hh0 =>
    exact hold_mint hl ihm ih hm hpend hh0
  | @mintReturn h i m hm hpend _ hh0 =>
    exact hold_mint hl ihm ih hm hpend hh0
  | @failDeposit i m hm hpend _ =>
    refine ⟨fun j m' hm' => ?_, fun cq => (ih cq).congr rfl ?_⟩
    · simp only [upd] at hm'; split_ifs at hm' with hj
      · cases hm'; exact ihm i m hm
      · exact ihm j m' hm'
    · refine holds_congr (fun _ => rfl) (fun j => ?_)
      simp only [upd]; split_ifs with hj
      · subst hj; simp [hm, Msg.Live, hpend]
      · exact Iff.rfl
  | @confirm i m f hm _ hf hs hreg =>
    refine ⟨fun j m' hm' => ?_, fun cq => ?_⟩
    · cases f <;> simp only [confirmPost, upd, ite_true, ite_false, Bool.false_eq_true] at hm' ⊢ <;>
        (split_ifs at hm' with hj
         · cases hm'; first | exact hreg | simp [upd2_apply, hreg]
         · first | exact ihm j m' hm' | (have := ihm j m' hm'; simp [upd2_apply, this]))
    · cases f
      · -- success: the message was executed, not live, before and after
        have hst : m.status = .executed := hs rfl
        refine (ih cq).congr rfl (holds_congr (fun _ => rfl) (fun j => ?_))
        simp only [confirmPost, upd, Bool.false_eq_true, ite_false]
        split_ifs with hj
        · subst hj; simp [hm, Msg.Live, hst]
        · exact Iff.rfl
      · have hfl : m.status = .failed := hf rfl
        by_cases hc : cq = m.chain
        · subst hc
          have hmsg : Holds s m.chain (.msg i) := ⟨m, hm, rfl, Or.inr hfl⟩
          have hu := (ih m.chain).unique hmsg
          refine ⟨fun _ => ⟨.hub W.l1, fun y => ?_⟩, fun h => by
            simp [confirmPost, hreg] at h⟩
          cases y with
          | hub h' =>
            simp only [Holds, confirmPost, upd2_apply, ite_true]
            by_cases hh : h' = W.l1
            · subst hh; simp [hl]
            · have := hu (.hub h'); simp only [Holds] at this
              simp [hh, this]
          | msg j =>
            simp only [Holds, confirmPost, upd, ite_true]
            by_cases hj : j = i
            · subst hj; simp [Msg.Live]
            · have := hu (.msg j); simp only [Holds] at this
              simp [hj, this]
        · refine (ih cq).congr rfl (holds_congr
            (fun h' => by simp [confirmPost, upd2_apply, Ne.symm hc, hc]) (fun j => ?_))
          simp only [confirmPost, upd, ite_true]
          split_ifs with hj
          · subst hj; simp [hm, Ne.symm hc]
          · exact Iff.rfl
  | pauseMigration => exact ⟨ihm, ih⟩
  | unpauseMigration => exact ⟨ihm, ih⟩
  | pauseCTM => exact ⟨ihm, ih⟩
  | unpauseCTM => exact ⟨ihm, ih⟩
  | pause => exact ⟨ihm, ih⟩
  | unpause => exact ⟨ihm, ih⟩
  | ctmUpgrade => exact ⟨ihm, ih⟩
  | diamondUpgrade => exact ⟨ihm, ih⟩

/-! ## Layer 4: unconfirmed L1 departures and `isMigrationInProgress` -/

/-- Message `i` is an L1-originated migration message for `c` not yet consumed. -/
def ND (W : World) (s : Sys) (c : ChainId) (i : ℕ) : Prop :=
  ∃ m, s.msgs i = some m ∧ m.src = W.l1 ∧ m.chain = c ∧ m.status ≠ .done

/-- The invariant behind `isMigrationInProgress[c]`. -/
def L1Msg (W : World) (s : Sys) (c : ChainId) : Prop :=
  (s.inProgress c = true ↔ ∃ i, ND W s c i) ∧
  ∀ i, ND W s c i → s.migNum W.l1 c ≠ 0 ∧ ∀ j, ND W s c j → j = i

theorem L1Msg.congr {W : World} {s s' : Sys} {c : ChainId} (h : L1Msg W s c)
    (hip : s'.inProgress c = s.inProgress c) (hnd : ∀ i, ND W s' c i ↔ ND W s c i)
    (hn : s.migNum W.l1 c ≠ 0 → s'.migNum W.l1 c ≠ 0) : L1Msg W s' c := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [hip, h.1]; exact exists_congr (fun i => (hnd i).symm)
  · obtain ⟨hn0, hu⟩ := h.2 i ((hnd i).1 hi)
    exact ⟨hn hn0, fun j hj => hu j ((hnd j).1 hj)⟩

/-- Changing the status of message `i` between two not-consumed values keeps `ND`. -/
theorem nd_status {W : World} {s : Sys} {c : ChainId} {i : ℕ} {m : Msg} {st : MsgStatus}
    (hm : s.msgs i = some m) (hst : m.status ≠ .done) (hst' : st ≠ .done) (j : ℕ) :
    ND W { s with msgs := upd s.msgs i (some { m with status := st }) } c j ↔ ND W s c j := by
  simp only [ND, upd]
  split_ifs with hj
  · subst hj; simp [hm, hst, hst']
  · exact Iff.rfl

theorem l1msg_inv {W : World} : ∀ s, Reach W s → ∀ c, L1Msg W s c := by
  refine reach_induction _ (fun s hi c => ⟨by simp [hi.inProgress, ND, hi.msgs],
    fun i hi' => by obtain ⟨m, hm, _⟩ := hi'; simp [hi.msgs] at hm⟩) ?_
  intro s l s' hreach ih hst c
  cases hst with
  | @register c0 x =>
    exact (ih c).congr rfl (fun _ => Iff.rfl) (fun h => by simpa [registerPost] using h)
  | @burn h c0 t a o _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hl1 =>
    have hfresh := fresh_inv s hreach s.nMsgs le_rfl
    by_cases hp : h = W.l1 ∧ c = c0
    · obtain ⟨rfl, rfl⟩ := hp
      have hn0 : s.migNum W.l1 c = 0 := by have := (hl1 rfl).2; simp [numToSL] at this; omega
      have hnone : ∀ j, ¬ ND W s c j := fun j hj => ((ih c).2 j hj).1 hn0
      have hnd : ∀ j, ND W (burnPost W s W.l1 c t a) c j ↔ j = s.nMsgs := by
        intro j
        simp only [ND, burnPost, upd]
        split_ifs with hj
        · simp [burnMsg, hj]
        · simp only [hj, iff_false]; exact hnone j
      refine ⟨⟨fun _ => ⟨s.nMsgs, (hnd _).2 rfl⟩, fun _ => by simp [burnPost, upd]⟩,
        fun i hi => ⟨by simp [burnPost, upd2_apply], fun j hj => ?_⟩⟩
      rw [(hnd i).1 hi, (hnd j).1 hj]
    · refine (ih c).congr ?_ (fun j => ?_) ?_
      · by_cases hh : h = W.l1
        · have hc : c ≠ c0 := fun hc => hp ⟨hh, hc⟩
          simp [burnPost, hh, upd, hc]
        · simp [burnPost, hh]
      · simp only [ND, burnPost, upd]
        split_ifs with hj
        · subst hj
          simp only [hfresh, Option.some.injEq, burnMsg, reduceCtorEq, false_and, exists_false,
            iff_false]
          rintro ⟨m, rfl, h1, h2, _⟩
          exact hp ⟨h1, h2.symm⟩
        · exact Iff.rfl
      · intro hn
        simp only [burnPost, upd2_apply]
        split_ifs with hq
        · exact absurd ⟨hq.1.symm, hq.2⟩ hp
        · exact hn
  | @mintFresh h i m hm hpend _ _ _ _ _ _ _ _ _ _ _ _ hnl =>
    refine (ih c).congr rfl (nd_status hm (by simp [hpend]) (by simp)) (fun hn => ?_)
    simp only [mintPost, upd2_apply]
    split_ifs with hq
    · exact absurd hq.1.symm hnl
    · exact hn
  | @mintReturn h i m hm hpend _ _ _ _ _ _ hl1 =>
    refine (ih c).congr rfl (nd_status hm (by simp [hpend]) (by simp)) (fun hn => ?_)
    simp only [mintPost, upd2_apply]
    split_ifs with hq
    · rw [(hl1 hq.1.symm).2]; simp [numToL1]
    · exact hn
  | @failDeposit i m hm hpend _ =>
    exact (ih c).congr rfl (nd_status hm (by simp [hpend]) (by simp)) id
  | @confirm i m f hm hsrc hf hs =>
    have hmnd : m.status ≠ .done := by
      cases f
      · simp [hs rfl]
      · simp [hf rfl]
    by_cases hc : c = m.chain
    · subst hc
      have hndi : ND W s m.chain i := ⟨m, hm, hsrc, rfl, hmnd⟩
      have hu := ((ih m.chain).2 i hndi).2
      have hnone : ∀ j, ¬ ND W (confirmPost W s i m f) m.chain j := by
        intro j hj
        obtain ⟨m', hm', h1, h2, h3⟩ := hj
        cases f <;> simp only [confirmPost, upd, Bool.false_eq_true, ite_false, ite_true] at hm' <;>
        (split_ifs at hm' with hji
         · cases hm'; exact h3 rfl
         · exact hji (hu j ⟨m', hm', h1, h2, h3⟩))
      refine ⟨⟨fun h => ?_, fun ⟨j, hj⟩ => absurd hj (hnone j)⟩, fun j hj => absurd hj (hnone j)⟩
      cases f <;> simp [confirmPost, upd] at h
    · refine (ih c).congr ?_ (fun j => ?_) ?_
      · cases f <;> simp [confirmPost, upd, hc]
      · have : ∀ st : MsgStatus,
            ND W { s with msgs := upd s.msgs i (some { m with status := st }) } c j ↔ ND W s c j := by
          intro st
          simp only [ND, upd]
          split_ifs with hj
          · subst hj; simp [hm, Ne.symm hc]
          · exact Iff.rfl
        cases f
        · exact this .done
        · simp only [ND, confirmPost, ite_true, upd] at this ⊢
          exact this .done
      · intro hn
        cases f
        · exact hn
        · simp only [confirmPost, ite_true, upd2_apply]
          split_ifs with hq
          · exact absurd hq.2 hc
          · exact hn
  | pauseMigration => exact ih c
  | unpauseMigration => exact ih c
  | pauseCTM => exact ih c
  | unpauseCTM => exact ih c
  | pause => exact ih c
  | unpause => exact ih c
  | ctmUpgrade => exact ih c
  | diamondUpgrade => exact ih c

/-! ## The properties -/

theorem ExactlyOneSettlementLayer : Properties.ExactlyOneSettlementLayer := by
  intro W s hl hr c
  exact (hold_inv hl s hr).2 c

theorem BridgehubAgreesWithDiamond : Properties.BridgehubAgreesWithDiamond := by
  intro W s hl hr h c hreg
  exact agree_inv hl s hr h c hreg

/-- A nonzero L1 migration number means the chain is registered on L1. -/
theorem reg_of_num {W : World} {s : Sys} {c : ChainId} (hb : Book W s c)
    (hn : s.migNum W.l1 c ≠ 0) : s.reg W.l1 c = true := by
  by_contra h; exact hn (hb.2.1 (by simpa using h))

theorem L1MigrationBookkeeping : Properties.L1MigrationBookkeeping := by
  intro W s hl hr c
  have hb := book_inv s hr c
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := id hb
  refine ⟨h1, h2, h3, h4, h5, h6, fun hreg => ?_⟩
  simp only [Holds]
  constructor
  · rintro ⟨_, hsl⟩ hn; exact (h5 hn).2.2 hsl
  · intro hn
    refine ⟨hl, ?_⟩
    have : s.migNum W.l1 c = 0 ∨ s.migNum W.l1 c = numToL1 := by
      simp only [maxMigrations, numToSL, numToL1] at h1 hn ⊢; omega
    rcases this with h | h
    · exact h4 h hreg
    · exact (h6 h).2

theorem L1MigrationNumberTransitions : Properties.L1MigrationNumberTransitions := by
  intro W s s' l c hst hne
  cases hst with
  | @register c0 x => exact absurd rfl hne
  | @burn h c0 t a o _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hl1 =>
    simp only [burnPost, upd2_apply] at hne ⊢
    split_ifs at hne ⊢ with hq
    · obtain ⟨rfl, rfl⟩ := hq
      have hn := (hl1 rfl).2
      left; refine ⟨by simp [numToSL] at hn; omega, hn, rfl, rfl⟩
    · exact absurd rfl hne
  | @mintFresh h i m _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnl =>
    simp only [mintPost, upd2_apply] at hne
    split_ifs at hne with hq
    · exact absurd hq.1.symm hnl
    · exact absurd rfl hne
  | @mintReturn h i m _ _ _ _ _ _ _ _ hl1 =>
    simp only [mintPost, upd2_apply] at hne ⊢
    split_ifs at hne ⊢ with hq
    · obtain ⟨rfl, rfl⟩ := hq
      obtain ⟨hn, hmn⟩ := hl1 rfl
      right; left; exact ⟨hn, hmn, by simp [Label.mintsOnL1]⟩
    · exact absurd rfl hne
  | failDeposit => exact absurd rfl hne
  | @confirm i m f _ _ _ _ _ _ hnum =>
    cases f
    · exact absurd rfl hne
    · simp only [confirmPost, ite_true, upd2_apply] at hne ⊢
      split_ifs at hne ⊢ with hq
      · obtain ⟨-, rfl⟩ := hq
        have hn := hnum rfl
        right; right; exact ⟨hn, by simp [hn, numToSL], i, rfl⟩
      · exact absurd rfl hne
  | pauseMigration => exact absurd rfl hne
  | unpauseMigration => exact absurd rfl hne
  | pauseCTM => exact absurd rfl hne
  | unpauseCTM => exact absurd rfl hne
  | pause => exact absurd rfl hne
  | unpause => exact absurd rfl hne
  | ctmUpgrade => exact absurd rfl hne
  | diamondUpgrade => exact absurd rfl hne

/-- L1's migration number 2 is absorbing. -/
theorem num_two_stays {W : World} {s s' : Sys} {l : Label} {c : ChainId} (hst : Step W s l s')
    (h2 : s.migNum W.l1 c = numToL1) : s'.migNum W.l1 c = numToL1 := by
  by_contra hne
  rcases L1MigrationNumberTransitions W s s' l c hst (by rw [h2]; exact hne) with
    ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h2, numToSL, numToL1] at h

/-- On a reachable state where L1's number of `c` is 2, L1 is `c`'s only holder. -/
theorem returned_holder {W : World} {s : Sys} {c : ChainId} (hl : W.l1 ≠ 0) (hr : Reach W s)
    (h2 : s.migNum W.l1 c = numToL1) : ∀ y, Holds s c y ↔ y = .hub W.l1 := by
  have hb := book_inv s hr c
  have hreg := reg_of_num hb (by rw [h2]; simp [numToL1])
  exact ((hold_inv hl s hr).2 c).unique ⟨hl, (hb.2.2.2.2.2 h2).2⟩

theorem ReturnedChainStaysOnL1 : Properties.ReturnedChainStaysOnL1 := by
  intro W s s' ls c hl hr hrun h2
  induction hrun with
  | nil => exact ⟨h2, returned_holder hl hr h2, fun l hl' => by simp at hl'⟩
  | @cons s0 s1 s2 l ls hst _ ih =>
    have h2' := num_two_stays hst h2
    obtain ⟨hA, hB, hC⟩ := ih (Reach.step hr hst) h2'
    refine ⟨hA, hB, fun l' hl' => ?_⟩
    rcases List.mem_cons.1 hl' with rfl | hmem
    · intro hmv
      have hu := returned_holder hl hr h2
      cases hst with
      | @burn h c0 t a o hh0 _ _ _ _ _ _ _ hsl _ _ _ _ _ _ _ _ _ hl1 =>
        simp only [Label.movesChain] at hmv; subst hmv
        have := (hu (.hub h)).1 ⟨hh0, hsl⟩
        cases this
        have := (hl1 rfl).2; rw [h2] at this; simp [numToL1, numToSL] at this
      | @mintFresh h i m hm hpend =>
        simp only [Label.movesChain] at hmv; subst hmv
        exact absurd ((hu (.msg i)).1 ⟨m, hm, rfl, Or.inl hpend⟩) (by simp)
      | @mintReturn h i m hm hpend =>
        simp only [Label.movesChain] at hmv; subst hmv
        exact absurd ((hu (.msg i)).1 ⟨m, hm, rfl, Or.inl hpend⟩) (by simp)
      | _ => simp [Label.movesChain] at hmv
    · exact hC l' hmem

theorem AtMostOneRoundTrip : Properties.AtMostOneRoundTrip := by
  intro W s s' ls c hl hr hrun
  induction hrun with
  | nil => simp [countL1Mints]; split_ifs <;> simp
  | @cons s0 s1 s2 l ls hst _ ih =>
    have ih' := ih (Reach.step hr hst)
    simp only [countL1Mints, List.filter_cons] at ih' ⊢
    by_cases hm : l.mintsOnL1 W c = true
    · -- the step is an L1 mint of `c`: the number goes 1 → 2
      have hpre : s0.migNum W.l1 c = numToSL ∧ s1.migNum W.l1 c = numToL1 := by
        cases hst with
        | @mintFresh h i m _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnl =>
          simp [Label.mintsOnL1] at hm; exact absurd hm.1 hnl
        | @mintReturn h i m _ _ _ _ _ _ _ _ hl1 =>
          simp [Label.mintsOnL1] at hm; obtain ⟨rfl, rfl⟩ := hm
          obtain ⟨hn, hmn⟩ := hl1 rfl
          exact ⟨hn, by simp [mintPost, upd2_apply, hmn]⟩
        | _ => simp [Label.mintsOnL1] at hm
      rw [if_pos hm, if_neg (by rw [hpre.1]; simp [numToSL, numToL1])]
      rw [if_pos hpre.2] at ih'
      simp only [List.length_cons]; omega
    · rw [if_neg hm]
      by_cases h2 : s0.migNum W.l1 c = numToL1
      · rw [if_pos (num_two_stays hst h2)] at ih'; rw [if_pos h2]; exact ih'
      · rw [if_neg h2]; split_ifs at ih' <;> omega

/-- The burn of a reachable state, inverted. -/
theorem FailedMigrationRecoveryRestoresSource :
    Properties.FailedMigrationRecoveryRestoresSource := by
  intro W s s1 c t a orig hl hr hst
  cases hst with
  | burn _ _ _ _ _ hctm _ _ _ _ hreg _ hdpv _ _ _ haway _ hl1 =>
    obtain ⟨_, hn⟩ := hl1 rfl
    have hn0 : s.migNum W.l1 c = 0 := by simp [numToSL] at hn; omega
    have hb := book_inv s hr c
    obtain ⟨hiv, hivsl⟩ := hb.2.2.1 hn0
    have hip : s.inProgress c = false := by
      have h1 := ((l1msg_inv s hr c).1)
      by_contra hc
      obtain ⟨j, hj⟩ := h1.1 (by simpa using hc)
      exact ((l1msg_inv s hr c).2 j hj).1 hn0
    set b := burnMsg s W.l1 c t a with hbdef
    let s2 : Sys := { burnPost W s W.l1 c t a with
      msgs := upd (burnPost W s W.l1 c t a).msgs s.nMsgs (some { b with status := .failed }) }
    have hfail : Step W (burnPost W s W.l1 c t a) (.failDeposit s.nMsgs) s2 :=
      Step.failDeposit (m := b) (by simp [burnPost, b]) rfl rfl
    have hconf : Step W s2 (.confirm s.nMsgs c true)
        (confirmPost W s2 s.nMsgs { b with status := .failed } true) :=
      Step.confirm (m := { b with status := .failed }) (by simp [s2]) rfl (fun _ => rfl)
        (fun h => by simp at h) (by simpa [s2, burnPost, b, burnMsg] using hreg)
        (by simpa [s2, burnPost, b, burnMsg] using hctm)
        (fun _ => by simp [s2, burnPost, b, burnMsg, upd2_apply, hn])
        (fun _ => by simp [s2, burnPost, b, burnMsg, upd2_apply])
        (fun _ => by simp [s2, burnPost, b, burnMsg])
    refine ⟨s2, _, hfail, hconf, ?_⟩
    simp only [confirmPost, ite_true, s2, burnPost, b, burnMsg]
    congr 1
    · funext h' c'; simp only [upd2_apply]; split_ifs with h1 h2 <;> simp_all
    · funext h' c'; simp only [upd2_apply]; split_ifs with h1 h2 <;> simp_all
    · funext c'; simp only [upd]; split_ifs with h1 <;> simp_all
    · funext c'; simp only [upd]; split_ifs with h1 <;> simp_all
    · funext c'; simp only [upd]; split_ifs with h1 <;> simp_all
    · funext h' c'; simp only [upd2_apply]; split_ifs with h1 h2 <;> simp_all
    · funext j; simp only [upd]; split_ifs <;> simp_all

theorem InProgressTracksUnconfirmedDeparture :
    Properties.InProgressTracksUnconfirmedDeparture := by
  intro W s hl hr c
  have h := l1msg_inv s hr c
  refine ⟨?_, fun i j m m' hm hm' hs hs' hc hc' hd hd' => ?_⟩
  · rw [h.1]; simp only [ND]
  · exact ((h.2 i ⟨m, hm, hs, hc, hd⟩).2 j ⟨m', hm', hs', hc', hd'⟩).symm

theorem VersionEqualityAtBurnAndMint : Properties.VersionEqualityAtBurnAndMint := by
  intro W s s' l hst
  refine ⟨fun h c t a orig hl => ?_, fun h i c a hl => ?_⟩
  · subst hl
    cases hst with
    | burn _ _ _ _ _ _ _ _ _ _ _ _ hdpv =>
      exact ⟨hdpv, burnMsg s h c t a, by simp [burnPost], rfl, rfl⟩
  · subst hl
    cases hst with
    | @mintFresh _ _ m hm =>
      refine ⟨m, hm, rfl, by simp [mintPost, upd2_apply], by simp [mintPost, upd2_apply],
        fun _ => ?_⟩
      assumption
    | @mintReturn _ _ m hm _ _ _ _ _ _ _ _ _ _ _ hreg hdpv =>
      refine ⟨m, hm, rfl, by simp [mintPost, upd2_apply], ?_, fun h => by simp [hreg] at h⟩
      simp [mintPost, upd2_apply, hdpv]

theorem MigrationsDisabledFreezeSettlement : Properties.MigrationsDisabledFreezeSettlement := by
  intro W s hl hen hr
  have key : ∀ s, Reach W s → (∀ i, s.msgs i = none) ∧ (∀ h c, s.migNum h c = 0) ∧
      (∀ h c, h ≠ W.l1 → s.sl h c = 0) ∧ (∀ c, s.reg W.l1 c = true → s.sl W.l1 c = W.l1) := by
    refine reach_induction _ (fun s hi => ⟨hi.msgs, hi.migNum, fun h c _ => hi.sl h c,
      fun c h => by simp [hi.reg] at h⟩) ?_
    intro s l s' _ ⟨hm, hn, hsl, hreg⟩ hst
    cases hst with
    | @register c0 x =>
      refine ⟨hm, hn, fun h c hh => ?_, fun c h => ?_⟩
      · simp [registerPost, upd2_apply, hh, hsl h c hh]
      · simp only [registerPost, upd2_apply] at h ⊢
        split_ifs at h ⊢ with hq
        · rfl
        · exact hreg c (by simpa [hq] using h)
    | burn _ _ he => simp [hen] at he
    | mintFresh _ _ _ _ _ he => simp [hen] at he
    | mintReturn _ _ _ _ _ he => simp [hen] at he
    | failDeposit hm' => simp [hm] at hm'
    | confirm hm' => simp [hm] at hm'
    | pauseMigration => exact ⟨hm, hn, hsl, hreg⟩
    | unpauseMigration => exact ⟨hm, hn, hsl, hreg⟩
    | pauseCTM => exact ⟨hm, hn, hsl, hreg⟩
    | unpauseCTM => exact ⟨hm, hn, hsl, hreg⟩
    | pause => exact ⟨hm, hn, hsl, hreg⟩
    | unpause => exact ⟨hm, hn, hsl, hreg⟩
    | ctmUpgrade => exact ⟨hm, hn, hsl, hreg⟩
    | diamondUpgrade => exact ⟨hm, hn, hsl, hreg⟩
  obtain ⟨hm, hn, hsl, hreg⟩ := key s hr
  refine ⟨hm, hn, fun c hc y => ?_⟩
  cases y with
  | hub h =>
    simp only [Holds, Holder.hub.injEq]
    by_cases hh : h = W.l1
    · subst hh; simp [hl, hreg c hc]
    · simp only [hh, iff_false, not_and]
      intro h0; rw [hsl h c hh]; exact Ne.symm h0
  | msg j => simp [Holds, hm]

end Contracts.ChainAssetHandler
