import EraSpec.Contracts.ChainAssetHandler.Properties.Migration

/-!
# Proofs: where a chain settles, its migration number, and recovery

The reachability results are inductive invariants over `Reach`, proved in layers: message
ids are fresh (`msgIds_fresh_inv`); L1's bookkeeping (`l1Book_inv`); bridgehub/diamond
agreement (`diamondAgree_inv`); the holder invariant (`holder_inv`), which uses freshness;
the L1-message invariant behind `isMigrationInProgress` (`l1Departure_inv`), which uses
freshness; the shape of messages and registrations (`shape_inv`); a chain is registered only on
L1 until it reaches a settlement layer (`elsewhere_inv`); and L1's bridgehub view of the holder
(`l1View_inv`). The last three use the earlier ones on the pre-state. Each layer is proved by
`reach_induction`, case by case over the steps. The enabledness results build the step from
these invariants. The witnesses are concrete runs of `cahWorld`, checked by evaluation.
-/

namespace Contracts.ChainAssetHandler

/-! ## Generic -/

@[simp] theorem upd_self {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) :
    upd f a b a = b := by simp [upd]

theorem upd_of_ne {α β : Type} [DecidableEq α] (f : α → β) {a x : α} (b : β) (h : x ≠ a) :
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

/-- `setSettlementLayerChainId` on `h` writes only hub `h`'s number for chain `h`. -/
theorem slChainIdPost_migNum {W : World} {s : Sys} {h p q h' c : ChainId}
    (hne : ¬ (h' = h ∧ c = h)) : (slChainIdPost W s h p q).migNum h' c = s.migNum h' c := by
  simp only [slChainIdPost]
  split_ifs
  · rfl
  · simp [upd2_apply, hne]

/-- A burn, inverted. -/
theorem burn_inv {W : World} {s s' : Sys} {h c t : ChainId} {a : AssetId}
    (hst : Step W s (.burn h c t a) s') : BurnOk W s h c t a ∧ s' = burnPost W s h c t a := by
  cases hst with
  | burn hg => exact ⟨hg, rfl⟩

/-- A mint, inverted. -/
theorem mint_inv {W : World} {s s' : Sys} {h : ChainId} {i : ℕ} {c : ChainId} {a : AssetId}
    (hst : Step W s (.mint h i c a) s') :
    ∃ m, MintOk W s h i m ∧ m.chain = c ∧ m.asset = a ∧
      ((s.reg h c = false ∧ m.pv = s.ctmPV h (W.ctmOfAsset h a) ∧ h ≠ W.l1 ∧
          s' = mintPost W s h i m (W.ctmOfAsset h a) true) ∨
        (s.reg h c = true ∧ s.dpv h c = s.ctmPV h (s.dctm h c) ∧ s.away h c = true ∧
          s' = mintPost W s h i m (W.ctmOfAsset h a) false)) := by
  cases hst with
  | @mintFresh _ _ m hg hnew hpv hl2 => exact ⟨m, hg, rfl, rfl, Or.inl ⟨hnew, hpv, hl2, rfl⟩⟩
  | @mintReturn _ _ m hg hold hpv haway =>
    exact ⟨m, hg, rfl, rfl, Or.inr ⟨hold, hpv, haway, rfl⟩⟩

/-- The destination of a burn is not its hub. -/
theorem BurnOk.dst_ne {W : World} {s : Sys} {h c t : ChainId} {a : AssetId}
    (hg : BurnOk W s h c t a) : t ≠ h := by
  by_cases hh : h = W.l1
  · exact hh ▸ (hg.l1Record hh).1
  · rw [hg.toL1 hh]; exact Ne.symm hh

/-! ## Layer 0: message ids are fresh -/

theorem msgIds_fresh_inv {W : World} :
    ∀ s, Reach W s → ∀ i, s.nMsgs ≤ i → s.msgs i = none := by
  refine reach_induction _ (fun s hi i _ => hi.msgs i) ?_
  intro s l s' _ ih hst
  cases hst with
  | burn =>
    intro i hi
    simp only [burnPost] at hi ⊢
    rw [upd_of_ne _ _ (by omega)]
    exact ih i (by omega)
  | @mintFresh _ j m hg =>
    intro i hi
    have hj : i ≠ j := by
      rintro rfl; have h1 := hg.msgAt; rw [ih _ hi] at h1; cases h1
    simp only [mintPost] at hi ⊢
    rw [upd_of_ne _ _ hj]; exact ih i hi
  | @mintReturn _ j m hg =>
    intro i hi
    have hj : i ≠ j := by
      rintro rfl; have h1 := hg.msgAt; rw [ih _ hi] at h1; cases h1
    simp only [mintPost] at hi ⊢
    rw [upd_of_ne _ _ hj]; exact ih i hi
  | @failDeposit j m hm =>
    intro i hi
    have hj : i ≠ j := by rintro rfl; rw [ih _ hi] at hm; cases hm
    simp only at hi ⊢
    rw [upd_of_ne _ _ hj]; exact ih i hi
  | @confirm j m f hg =>
    intro i hi
    have hi' : s.nMsgs ≤ i := by cases f <;> exact hi
    have hj : i ≠ j := by
      rintro rfl; have h1 := hg.msgAt; rw [ih _ hi'] at h1; cases h1
    cases f <;> simp [confirmPost, upd, hj, ih i hi']
  | createChain => exact ih
  | registerDeployed => exact ih
  | setSLChainId => exact ih
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

/-- Registering chain `c0` on L1 (either path) keeps L1's bookkeeping. -/
theorem book_register {W : World} {s s' : Sys} {c c0 : ChainId} (hb : Book W s c)
    (hnr : s.reg W.l1 c0 = false) (hsl : s'.sl = upd2 s.sl W.l1 c0 W.l1)
    (hreg : s'.reg = upd2 s.reg W.l1 c0 true) (hn : s'.migNum = s.migNum)
    (ha : s'.ivActive = s.ivActive) (hs : s'.ivSL = s.ivSL) : Book W s' c := by
  obtain ⟨_, h2, h3, _, _, _⟩ := id hb
  by_cases hc : c = c0
  · subst hc
    have h0 := h2 hnr
    exact book_zero (by rw [hn]; exact h0) (by rw [ha]; exact (h3 h0).1)
      (by rw [hs]; exact (h3 h0).2) (fun _ => by rw [hsl]; simp [upd2_apply])
  · exact hb.congr (by rw [hn]) (by rw [hreg]; simp [upd2_apply, hc]) (by rw [ha])
      (by rw [hs]) (by rw [hsl]; simp [upd2_apply, hc])

theorem l1Book_inv {W : World} : ∀ s, Reach W s → ∀ c, Book W s c := by
  refine reach_induction _ (fun s hi c => ?_) ?_
  · exact book_zero (hi.migNum _ _) (hi.ivActive _) (hi.ivSL _) (by simp [hi.reg])
  intro s l s' _ ih hst c
  have hb := ih c
  cases hst with
  | @createChain c0 x hg => exact book_register hb hg.notRegistered rfl rfl rfl rfl rfl
  | @registerDeployed c0 hg => exact book_register hb hg.notRegistered rfl rfl rfl rfl rfl
  | @burn h c0 t a hg =>
    by_cases hh : h = W.l1
    · subst hh
      obtain ⟨htl, hn⟩ := hg.l1Record rfl
      by_cases hc : c = c0
      · subst hc
        exact book_one (by simp [burnPost, upd2_apply, hn])
          (by simpa [burnPost] using hg.registered)
          (by simp [burnPost]) (by simp [burnPost, upd2_apply])
          (by simpa [burnPost, upd2_apply] using htl)
      · exact hb.congr (by simp [burnPost, upd2_apply, hc]) rfl
          (by simp [burnPost, upd, hc]) (by simp [burnPost, upd, hc])
          (by simp [burnPost, upd2_apply, hc])
    · have hh' : W.l1 ≠ h := Ne.symm hh
      exact hb.congr (by simp [burnPost, upd2_apply, hh']) rfl (by simp [burnPost, hh])
        (by simp [burnPost, hh]) (by simp [burnPost, upd2_apply, hh'])
  | @mintFresh h i m hg hnew hpv hl2 =>
    have hh : W.l1 ≠ h := Ne.symm hl2
    exact hb.congr (by simp [mintPost, upd2_apply, hh]) (by simp [mintPost, upd2_apply, hh])
      (by simp [mintPost, hl2]) rfl (by simp [mintPost, upd2_apply, hh])
  | @mintReturn h i m hg hold hpv haway =>
    by_cases hh : h = W.l1
    · subst hh
      obtain ⟨_, hmn⟩ := hg.l1Numbers rfl
      by_cases hc : c = m.chain
      · subst hc
        exact book_two (by simp [mintPost, upd2_apply, hmn]) (by simp [mintPost, upd2_apply])
          (by simp [mintPost]) (by simp [mintPost, upd2_apply])
      · exact hb.congr (by simp [mintPost, upd2_apply, hc])
          (by simp [mintPost, upd2_apply, hc])
          (by simp [mintPost, upd, hc]) rfl (by simp [mintPost, upd2_apply, hc])
    · have hh' : W.l1 ≠ h := Ne.symm hh
      exact hb.congr (by simp [mintPost, upd2_apply, hh'])
        (by simp [mintPost, upd2_apply, hh'])
        (by simp [mintPost, hh]) rfl (by simp [mintPost, upd2_apply, hh'])
  | failDeposit => exact hb
  | @confirm i m f hg =>
    cases f
    · exact hb.congr rfl rfl rfl rfl rfl
    · have hn := hg.failNum rfl
      by_cases hc : c = m.chain
      · subst hc
        exact book_zero (by simp [confirmPost, upd2_apply, hn, numToSL])
          (by simp [confirmPost]) (by simp [confirmPost])
          (fun _ => by simp [confirmPost, upd2_apply])
      · exact hb.congr (by simp [confirmPost, upd2_apply, hc]) rfl
          (by simp [confirmPost, upd, hc]) (by simp [confirmPost, upd, hc])
          (by simp [confirmPost, upd2_apply, hc])
  | @setSLChainId h p q _ hl2 =>
    exact hb.congr (slChainIdPost_migNum (fun h' => hl2 h'.1.symm)) rfl rfl rfl rfl
  | pauseMigration => exact hb
  | unpauseMigration => exact hb
  | pauseCTM => exact hb
  | unpauseCTM => exact hb
  | pause => exact hb
  | unpause => exact hb
  | ctmUpgrade => exact hb
  | diamondUpgrade => exact hb

/-! ## Layer 2: the bridgehub and the diamond agree -/

theorem diamondAgree_inv {W : World} (hl : W.l1 ≠ 0) : ∀ s, Reach W s → ∀ h c,
    (s.reg h c = true → h ≠ 0 ∧ (s.sl h c = h ↔ s.away h c = false)) ∧
    (s.reg h c = false → s.away h c = false) := by
  refine reach_induction _
    (fun s hi h c => ⟨fun hr => by simp [hi.reg] at hr, fun _ => hi.away h c⟩) ?_
  intro s l s' _ ih hst hq cq
  cases hst with
  | @createChain c0 x hg =>
    by_cases hp : hq = W.l1 ∧ cq = c0
    · obtain ⟨rfl, rfl⟩ := hp
      simp [createPost, upd2_apply, hl]
    · simp only [createPost, upd2_apply, hp, ite_false]; exact ih hq cq
  | @registerDeployed c0 hg =>
    by_cases hp : hq = W.l1 ∧ cq = c0
    · obtain ⟨rfl, rfl⟩ := hp
      have haw := (ih W.l1 cq).2 hg.notRegistered
      simp [registerDeployedPost, upd2_apply, hl, haw]
    · simp only [registerDeployedPost, upd2_apply, hp, ite_false]; exact ih hq cq
  | @burn h c0 t a hg =>
    by_cases hp : hq = h ∧ cq = c0
    · obtain ⟨rfl, rfl⟩ := hp
      simp [burnPost, upd2_apply, hg.hubNonzero, hg.dst_ne, hg.registered]
    · simp only [burnPost, upd2_apply, hp, ite_false]; exact ih hq cq
  | @mintFresh h i m hg =>
    by_cases hp : hq = h ∧ cq = m.chain
    · obtain ⟨rfl, rfl⟩ := hp
      simp [mintPost, upd2_apply, hg.hubNonzero]
    · simp only [mintPost, upd2_apply, hp, ite_false]; exact ih hq cq
  | @mintReturn h i m hg =>
    by_cases hp : hq = h ∧ cq = m.chain
    · obtain ⟨rfl, rfl⟩ := hp
      simp [mintPost, upd2_apply, hg.hubNonzero]
    · simp only [mintPost, upd2_apply, hp, ite_false]; exact ih hq cq
  | failDeposit => exact ih hq cq
  | @confirm i m f hg =>
    cases f
    · exact ih hq cq
    · by_cases hp : hq = W.l1 ∧ cq = m.chain
      · obtain ⟨rfl, rfl⟩ := hp
        simp [confirmPost, upd2_apply, hl]
      · simp only [confirmPost, upd2_apply, hp, ite_false, ite_true]; exact ih hq cq
  | setSLChainId => exact ih hq cq
  | pauseMigration => exact ih hq cq
  | unpauseMigration => exact ih hq cq
  | pauseCTM => exact ih hq cq
  | unpauseCTM => exact ih hq cq
  | pause => exact ih hq cq
  | unpause => exact ih hq cq
  | ctmUpgrade => exact ih hq cq
  | diamondUpgrade => exact ih hq cq

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

/-- Registering chain `c0` on L1 (either path) makes L1 its unique holder. -/
theorem hold_register {W : World} {s s' : Sys} {c0 : ChainId} (hl : W.l1 ≠ 0)
    (ihm : ∀ i m, s.msgs i = some m → s.reg W.l1 m.chain = true) (ih : ∀ c, HoldInv W s c)
    (hnr : s.reg W.l1 c0 = false) (hsl : s'.sl = upd2 s.sl W.l1 c0 W.l1)
    (hreg : s'.reg = upd2 s.reg W.l1 c0 true) (hmsgs : s'.msgs = s.msgs) :
    (∀ i m, s'.msgs i = some m → s'.reg W.l1 m.chain = true) ∧ ∀ c, HoldInv W s' c := by
  refine ⟨fun i m hm => ?_, fun cq => ?_⟩
  · rw [hmsgs] at hm
    have := ihm i m hm
    rw [hreg]; simp only [upd2_apply]; split_ifs <;> simp_all
  · by_cases hc : cq = c0
    · subst hc
      refine ⟨fun _ => ⟨.hub W.l1, fun y => ?_⟩, fun h => by
        rw [hreg] at h; simp [upd2_apply] at h⟩
      have hno := (ih cq).2 hnr
      cases y with
      | hub h' =>
        by_cases hh : h' = W.l1
        · subst hh; simp [Holds, hsl, upd2_apply, hl]
        · have := hno (.hub h')
          simp only [Holds, hsl, upd2_apply, hh, false_and, ite_false] at this ⊢
          simp [this, hh]
      | msg j =>
        have := hno (.msg j)
        simpa [Holds, hmsgs] using this
    · refine (ih cq).congr (by rw [hreg]; simp [upd2_apply, hc]) ?_
      exact holds_congr (fun h => by rw [hsl]; simp [upd2_apply, hc])
        (fun j => by rw [hmsgs])

/-- A mint moves its chain from the message to the minting hub. -/
theorem hold_mint {W : World} {s : Sys} {h : ChainId} {i : ℕ} {m : Msg} {x : Address}
    {fresh : Bool}
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

theorem holder_inv {W : World} (hl : W.l1 ≠ 0) : ∀ s, Reach W s →
    (∀ i m, s.msgs i = some m → s.reg W.l1 m.chain = true) ∧ ∀ c, HoldInv W s c := by
  refine reach_induction _ (fun s hi => ⟨fun i m h => by simp [hi.msgs] at h,
    fun c => ⟨fun h => by simp [hi.reg] at h, fun _ y => ?_⟩⟩) ?_
  · cases y with
    | hub h => simp only [Holds, hi.sl]; exact fun ⟨h1, h2⟩ => h1 h2.symm
    | msg j => simp [Holds, hi.msgs]
  intro s l s' hreach ⟨ihm, ih⟩ hst
  cases hst with
  | @createChain c0 x hg => exact hold_register hl ihm ih hg.notRegistered rfl rfl rfl
  | @registerDeployed c0 hg => exact hold_register hl ihm ih hg.notRegistered rfl rfl rfl
  | @burn h c0 t a hg =>
    have hfresh := msgIds_fresh_inv s hreach s.nMsgs le_rfl
    have hhub : Holds s c0 (.hub h) := ⟨hg.hubNonzero, hg.settlesHere⟩
    have hregc := (ih c0).reg hhub
    have htne := hg.dst_ne
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
  | @mintFresh h i m hg =>
    exact hold_mint ihm ih hg.msgAt hg.pending hg.hubNonzero
  | @mintReturn h i m hg =>
    exact hold_mint ihm ih hg.msgAt hg.pending hg.hubNonzero
  | @failDeposit i m hm hpend _ =>
    refine ⟨fun j m' hm' => ?_, fun cq => (ih cq).congr rfl ?_⟩
    · simp only [upd] at hm'; split_ifs at hm' with hj
      · cases hm'; exact ihm i m hm
      · exact ihm j m' hm'
    · refine holds_congr (fun _ => rfl) (fun j => ?_)
      simp only [upd]; split_ifs with hj
      · subst hj; simp [hm, Msg.Live, hpend]
      · exact Iff.rfl
  | @confirm i m f hg =>
    have hm := hg.msgAt
    have hreg := hg.registered
    refine ⟨fun j m' hm' => ?_, fun cq => ?_⟩
    · cases f <;>
        simp only [confirmPost, upd, ite_true, ite_false, Bool.false_eq_true] at hm' ⊢ <;>
        (split_ifs at hm' with hj
         · cases hm'; exact hreg
         · exact ihm j m' hm')
    · cases f
      · -- success: the message was executed, not live, before and after
        have hst : m.status = .executed := hg.executed rfl
        refine (ih cq).congr rfl (holds_congr (fun _ => rfl) (fun j => ?_))
        simp only [confirmPost, upd, Bool.false_eq_true, ite_false]
        split_ifs with hj
        · subst hj; simp [hm, Msg.Live, hst]
        · exact Iff.rfl
      · have hfl : m.status = .failed := hg.failed rfl
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
            (fun h' => by simp [confirmPost, upd2_apply, hc]) (fun j => ?_))
          simp only [confirmPost, upd, ite_true]
          split_ifs with hj
          · subst hj; simp [hm, Ne.symm hc]
          · exact Iff.rfl
  | setSLChainId => exact ⟨ihm, ih⟩
  | pauseMigration => exact ⟨ihm, ih⟩
  | unpauseMigration => exact ⟨ihm, ih⟩
  | pauseCTM => exact ⟨ihm, ih⟩
  | unpauseCTM => exact ⟨ihm, ih⟩
  | pause => exact ⟨ihm, ih⟩
  | unpause => exact ⟨ihm, ih⟩
  | ctmUpgrade => exact ⟨ihm, ih⟩
  | diamondUpgrade => exact ⟨ihm, ih⟩

/-- On a reachable state, a holder of a chain is its unique holder. -/
theorem holds_unique {W : World} {s : Sys} {c : ChainId} {x : Holder} (hl : W.l1 ≠ 0)
    (hr : Reach W s) (hx : Holds s c x) : ∀ y, Holds s c y ↔ y = x :=
  ((holder_inv hl s hr).2 c).unique hx

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

theorem l1Departure_inv {W : World} : ∀ s, Reach W s → ∀ c, L1Msg W s c := by
  refine reach_induction _ (fun s hi c => ⟨by simp [hi.inProgress, ND, hi.msgs],
    fun i hi' => by obtain ⟨m, hm, _⟩ := hi'; simp [hi.msgs] at hm⟩) ?_
  intro s l s' hreach ih hst c
  cases hst with
  | createChain => exact (ih c).congr rfl (fun _ => Iff.rfl) id
  | registerDeployed => exact (ih c).congr rfl (fun _ => Iff.rfl) id
  | @burn h c0 t a hg =>
    have hfresh := msgIds_fresh_inv s hreach s.nMsgs le_rfl
    by_cases hp : h = W.l1 ∧ c = c0
    · obtain ⟨rfl, rfl⟩ := hp
      have hn0 : s.migNum W.l1 c = 0 := by
        have := (hg.l1Record rfl).2; simp [numToSL] at this; omega
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
  | @mintFresh h i m hg hnew hpv hl2 =>
    refine (ih c).congr rfl (nd_status hg.msgAt (by simp [hg.pending]) (by simp))
      (fun hn => ?_)
    simp only [mintPost, upd2_apply]
    split_ifs with hq
    · exact absurd hq.1.symm hl2
    · exact hn
  | @mintReturn h i m hg =>
    refine (ih c).congr rfl (nd_status hg.msgAt (by simp [hg.pending]) (by simp))
      (fun hn => ?_)
    simp only [mintPost, upd2_apply]
    split_ifs with hq
    · rw [(hg.l1Numbers hq.1.symm).2]; simp [numToL1]
    · exact hn
  | @failDeposit i m hm hpend _ =>
    exact (ih c).congr rfl (nd_status hm (by simp [hpend]) (by simp)) id
  | @confirm i m f hg =>
    have hm := hg.msgAt
    have hsrc := hg.fromL1
    have hmnd : m.status ≠ .done := by
      cases f
      · simp [hg.executed rfl]
      · simp [hg.failed rfl]
    by_cases hc : c = m.chain
    · subst hc
      have hndi : ND W s m.chain i := ⟨m, hm, hsrc, rfl, hmnd⟩
      have hu := ((ih m.chain).2 i hndi).2
      have hnone : ∀ j, ¬ ND W (confirmPost W s i m f) m.chain j := by
        intro j hj
        obtain ⟨m', hm', h1, h2, h3⟩ := hj
        cases f <;>
          simp only [confirmPost, upd, Bool.false_eq_true, ite_false, ite_true] at hm' <;>
          (split_ifs at hm' with hji
           · cases hm'; exact h3 rfl
           · exact hji (hu j ⟨m', hm', h1, h2, h3⟩))
      refine ⟨⟨fun h => ?_, fun ⟨j, hj⟩ => absurd hj (hnone j)⟩,
        fun j hj => absurd hj (hnone j)⟩
      cases f <;> simp [confirmPost, upd] at h
    · refine (ih c).congr ?_ (fun j => ?_) ?_
      · cases f <;> simp [confirmPost, upd, hc]
      · have : ∀ st : MsgStatus,
            ND W { s with msgs := upd s.msgs i (some { m with status := st }) } c j ↔
              ND W s c j := by
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
  | @setSLChainId h p q _ hl2 =>
    exact (ih c).congr rfl (fun _ => Iff.rfl)
      (fun hn => by rwa [slChainIdPost_migNum (fun h' => hl2 h'.1.symm)])
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
  exact (holder_inv hl s hr).2 c

theorem BridgehubAgreesWithDiamond : Properties.BridgehubAgreesWithDiamond := by
  intro W s hl hr h c
  exact diamondAgree_inv hl s hr h c

/-- A nonzero L1 migration number means the chain is registered on L1. -/
theorem reg_of_num {W : World} {s : Sys} {c : ChainId} (hb : Book W s c)
    (hn : s.migNum W.l1 c ≠ 0) : s.reg W.l1 c = true := by
  by_contra h; exact hn (hb.2.1 (by simpa using h))

theorem L1MigrationBookkeeping : Properties.L1MigrationBookkeeping := by
  intro W s hl hr c
  have hb := l1Book_inv s hr c
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
  | createChain => exact absurd rfl hne
  | registerDeployed => exact absurd rfl hne
  | @burn h c0 t a hg =>
    simp only [burnPost, upd2_apply] at hne ⊢
    split_ifs at hne ⊢ with hq
    · obtain ⟨rfl, rfl⟩ := hq
      have hn := (hg.l1Record rfl).2
      left; exact ⟨by simp [numToSL] at hn; omega, hn, rfl, rfl⟩
    · exact absurd rfl hne
  | @mintFresh h i m hg hnew hpv hl2 =>
    simp only [mintPost, upd2_apply] at hne
    split_ifs at hne with hq
    · exact absurd hq.1.symm hl2
    · exact absurd rfl hne
  | @mintReturn h i m hg =>
    simp only [mintPost, upd2_apply] at hne ⊢
    split_ifs at hne ⊢ with hq
    · obtain ⟨rfl, rfl⟩ := hq
      obtain ⟨hn, hmn⟩ := hg.l1Numbers rfl
      right; left; exact ⟨hn, hmn, by simp [Label.mintsOnL1]⟩
    · exact absurd rfl hne
  | failDeposit => exact absurd rfl hne
  | @confirm i m f hg =>
    cases f
    · exact absurd rfl hne
    · simp only [confirmPost, ite_true, upd2_apply] at hne ⊢
      split_ifs at hne ⊢ with hq
      · obtain ⟨-, rfl⟩ := hq
        have hn := hg.failNum rfl
        right; right; exact ⟨hn, by simp [hn, numToSL], i, rfl⟩
      · exact absurd rfl hne
  | @setSLChainId h p q _ hl2 =>
    exact absurd (slChainIdPost_migNum (fun h' => hl2 h'.1.symm)) hne
  | pauseMigration => exact absurd rfl hne
  | unpauseMigration => exact absurd rfl hne
  | pauseCTM => exact absurd rfl hne
  | unpauseCTM => exact absurd rfl hne
  | pause => exact absurd rfl hne
  | unpause => exact absurd rfl hne
  | ctmUpgrade => exact absurd rfl hne
  | diamondUpgrade => exact absurd rfl hne

/-- L1's migration number 2 is absorbing. -/
theorem num_two_stays {W : World} {s s' : Sys} {l : Label} {c : ChainId}
    (hst : Step W s l s') (h2 : s.migNum W.l1 c = numToL1) : s'.migNum W.l1 c = numToL1 := by
  by_contra hne
  rcases L1MigrationNumberTransitions W s s' l c hst (by rw [h2]; exact hne) with
    ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h2, numToSL, numToL1] at h

/-- On a reachable state where L1's number of `c` is 2, L1 is `c`'s only holder. -/
theorem returned_holder {W : World} {s : Sys} {c : ChainId} (hl : W.l1 ≠ 0) (hr : Reach W s)
    (h2 : s.migNum W.l1 c = numToL1) : ∀ y, Holds s c y ↔ y = .hub W.l1 := by
  have hb := l1Book_inv s hr c
  exact holds_unique hl hr ⟨hl, (hb.2.2.2.2.2 h2).2⟩

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
      | @burn h c0 t a hg =>
        simp only [Label.movesChain] at hmv; subst hmv
        have := (hu (.hub h)).1 ⟨hg.hubNonzero, hg.settlesHere⟩
        cases this
        have := (hg.l1Record rfl).2; rw [h2] at this; simp [numToL1, numToSL] at this
      | @mintFresh h i m hg =>
        simp only [Label.movesChain] at hmv; subst hmv
        exact absurd ((hu (.msg i)).1 ⟨m, hg.msgAt, rfl, Or.inl hg.pending⟩) (by simp)
      | @mintReturn h i m hg =>
        simp only [Label.movesChain] at hmv; subst hmv
        exact absurd ((hu (.msg i)).1 ⟨m, hg.msgAt, rfl, Or.inl hg.pending⟩) (by simp)
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
        | @mintFresh h i m hg hnew hpv hl2 =>
          simp [Label.mintsOnL1] at hm; exact absurd hm.1 hl2
        | @mintReturn h i m hg =>
          simp [Label.mintsOnL1] at hm; obtain ⟨rfl, rfl⟩ := hm
          obtain ⟨hn, hmn⟩ := hg.l1Numbers rfl
          exact ⟨hn, by simp [mintPost, upd2_apply, hmn]⟩
        | _ => simp [Label.mintsOnL1] at hm
      rw [ite_eq_left hm, ite_eq_right (by rw [hpre.1]; simp [numToSL, numToL1])]
      rw [ite_eq_left hpre.2] at ih'
      simp only [List.length_cons]; omega
    · rw [ite_eq_right hm]
      by_cases h2 : s0.migNum W.l1 c = numToL1
      · rw [ite_eq_left (num_two_stays hst h2)] at ih'; rw [ite_eq_left h2]; exact ih'
      · rw [ite_eq_right h2]; split_ifs at ih' <;> omega

theorem FailedMigrationRecoveryRestoresSource :
    Properties.FailedMigrationRecoveryRestoresSource := by
  intro W s s1 c t a hl hr hst
  obtain ⟨hg, rfl⟩ := burn_inv hst
  obtain ⟨_, hn⟩ := hg.l1Record rfl
  have hn0 : s.migNum W.l1 c = 0 := by simp [numToSL] at hn; omega
  have hb := l1Book_inv s hr c
  obtain ⟨hiv, hivsl⟩ := hb.2.2.1 hn0
  have hip : s.inProgress c = false := by
    have h1 := (l1Departure_inv s hr c).1
    by_contra hc
    obtain ⟨j, hj⟩ := h1.1 (by simpa using hc)
    exact ((l1Departure_inv s hr c).2 j hj).1 hn0
  set b := burnMsg s W.l1 c t a with hbdef
  let s2 : Sys := { burnPost W s W.l1 c t a with
    msgs := upd (burnPost W s W.l1 c t a).msgs s.nMsgs (some { b with status := .failed }) }
  have hfail : Step W (burnPost W s W.l1 c t a) (.failDeposit s.nMsgs) s2 :=
    Step.failDeposit (m := b) (by simp [burnPost, b]) rfl rfl
  have hconf : Step W s2 (.confirm s.nMsgs c true)
      (confirmPost W s2 s.nMsgs { b with status := .failed } true) :=
    Step.confirm (m := { b with status := .failed })
      { msgAt := by simp [s2]
        fromL1 := rfl
        failed := fun _ => rfl
        executed := fun h => by simp at h
        registered := by simpa [s2, burnPost, b, burnMsg] using hg.registered
        ctmSet := by simpa [s2, burnPost, b, burnMsg] using hg.ctmSet
        failNum := fun _ => by simp [s2, burnPost, b, burnMsg, upd2_apply, hn]
        failAway := fun _ => by simp [s2, burnPost, b, burnMsg, upd2_apply]
        failPv := fun _ => by simp [s2, burnPost, b, burnMsg] }
  refine ⟨s2, _, hfail, hconf, ?_⟩
  have hsl := hg.settlesHere
  have haway := hg.notAway
  simp only [confirmPost, ite_true, s2, burnPost, b, burnMsg]
  congr 1
  · funext h' c'; simp only [upd2_apply]; split_ifs with h1 <;> simp_all
  · funext h' c'; simp only [upd2_apply]; split_ifs with h1 <;> simp_all
  · funext c'; simp only [upd]; split_ifs with h1 <;> simp_all
  · funext c'; simp only [upd]; split_ifs with h1 <;> simp_all
  · funext c'; simp only [upd]; split_ifs with h1 <;> simp_all
  · funext h' c'; simp only [upd2_apply]; split_ifs with h1 <;> simp_all
  · funext j; simp only [upd]; split_ifs <;> simp_all

theorem InProgressTracksUnconfirmedDeparture :
    Properties.InProgressTracksUnconfirmedDeparture := by
  intro W s hl hr c
  have h := l1Departure_inv s hr c
  refine ⟨?_, fun i j m m' hm hm' hs hs' hc hc' hd hd' => ?_⟩
  · rw [h.1]; simp only [ND]
  · exact ((h.2 i ⟨m, hm, hs, hc, hd⟩).2 j ⟨m', hm', hs', hc', hd'⟩).symm

theorem VersionEqualityAtBurnAndMint : Properties.VersionEqualityAtBurnAndMint := by
  intro W s s' l hst
  refine ⟨fun h c t a hl => ?_, fun h i c a hl => ?_⟩
  · subst hl
    obtain ⟨hg, rfl⟩ := burn_inv hst
    exact ⟨hg.atCtmVersion, burnMsg s h c t a, by simp [burnPost], rfl, rfl⟩
  · subst hl
    obtain ⟨m, hg, rfl, rfl, hcase⟩ := mint_inv hst
    rcases hcase with ⟨_, hpv, _, rfl⟩ | ⟨hold, hpv, _, rfl⟩
    · exact ⟨m, hg.msgAt, rfl, by simp [mintPost, upd2_apply],
        by simp [mintPost, upd2_apply], fun _ => ⟨by simp [mintPost, upd2_apply], hpv⟩⟩
    · refine ⟨m, hg.msgAt, rfl, by simp [mintPost, upd2_apply], ?_,
        fun h => by simp [hold] at h⟩
      simp [mintPost, hpv]

theorem MigrationsDisabledFreezeSettlement : Properties.MigrationsDisabledFreezeSettlement := by
  intro W s hl hen hr
  have key : ∀ s, Reach W s → (∀ i, s.msgs i = none) ∧ (∀ h c, h ≠ c → s.migNum h c = 0) ∧
      (∀ h c, h ≠ W.l1 → s.sl h c = 0) ∧
      (∀ c, s.reg W.l1 c = true → s.sl W.l1 c = W.l1) := by
    refine reach_induction _ (fun s hi => ⟨hi.msgs, fun h c _ => hi.migNum h c,
      fun h c _ => hi.sl h c, fun c h => by simp [hi.reg] at h⟩) ?_
    intro s l s' _ ⟨hm, hn, hsl, hreg⟩ hst
    have hreg_register : ∀ c0 (s'' : Sys), s''.reg = upd2 s.reg W.l1 c0 true →
        s''.sl = upd2 s.sl W.l1 c0 W.l1 → ∀ c, s''.reg W.l1 c = true → s''.sl W.l1 c = W.l1 := by
      intro c0 s'' hr' hs' c h
      rw [hs']; rw [hr'] at h
      simp only [upd2_apply] at h ⊢
      split_ifs at h ⊢ with hq
      · rfl
      · exact hreg c (by simpa [hq] using h)
    have hsl_register : ∀ c0 (s'' : Sys), s''.sl = upd2 s.sl W.l1 c0 W.l1 →
        ∀ h c, h ≠ W.l1 → s''.sl h c = 0 := by
      intro c0 s'' hs' h c hh
      rw [hs']; simp [upd2_apply, hh, hsl h c hh]
    cases hst with
    | @createChain c0 x hg =>
      exact ⟨hm, hn, hsl_register c0 _ rfl, hreg_register c0 _ rfl rfl⟩
    | @registerDeployed c0 hg =>
      exact ⟨hm, hn, hsl_register c0 _ rfl, hreg_register c0 _ rfl rfl⟩
    | burn hg => exact absurd hg.enabled (by simp [hen])
    | mintFresh hg => exact absurd hg.enabled (by simp [hen])
    | mintReturn hg => exact absurd hg.enabled (by simp [hen])
    | failDeposit hm' => simp [hm] at hm'
    | confirm hg => have := hg.msgAt; simp [hm] at this
    | @setSLChainId h p q _ _ =>
      refine ⟨hm, fun h' c hne => ?_, hsl, hreg⟩
      rw [slChainIdPost_migNum (fun h'' => hne (h''.1.trans h''.2.symm))]
      exact hn h' c hne
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


/-! ## Layer 5: the shape of messages and registrations -/

/-- The shape of a migration message: the conclusion of `MessagesRunBetweenL1AndALayer`. -/
def MsgShape (W : World) (m : Msg) : Prop :=
  m.src ≠ 0 ∧ m.dst ≠ 0 ∧ W.wl m.src m.dst = true ∧ m.chain ≠ m.src ∧ m.chain ≠ m.dst ∧
    ((m.src = W.l1 ∧ m.dst ≠ W.l1 ∧ m.num = numToSL) ∨
      (m.dst = W.l1 ∧ m.src ≠ W.l1 ∧ m.num = numToL1))

/-- The layer-5 invariant. -/
structure Shape (W : World) (s : Sys) : Prop where
  /-- A hub never records a chain with its own id as settling on it. -/
  slSelf : ∀ h c, h ≠ 0 → s.sl h c = h → c ≠ h
  /-- A chain settling on a hub other than L1 has number 1 there. -/
  slNum : ∀ g c, g ≠ 0 → g ≠ W.l1 → s.sl g c = g → s.migNum g c = numToSL
  /-- A chain registered anywhere is registered on L1. -/
  regL1 : ∀ h c, s.reg h c = true → s.reg W.l1 c = true
  /-- A chain registered on L1 is neither `0` nor L1. -/
  regL1Id : ∀ c, s.reg W.l1 c = true → c ≠ 0 ∧ c ≠ W.l1
  /-- A registered chain has a CTM on that hub's bridgehub. -/
  regCtm : ∀ h c, s.reg h c = true → s.ctm h c ≠ 0
  /-- Every message has the shape. -/
  msg : ∀ i m, s.msgs i = some m → MsgShape W m

/-- Registering chain `c0` on L1 (either path) keeps the shape. -/
theorem shape_register {W : World} {s s' : Sys} {c0 : ChainId} {x : Address} (ih : Shape W s)
    (hc0 : c0 ≠ 0) (hl1 : c0 ≠ W.l1) (hx : x ≠ 0)
    (hsl : s'.sl = upd2 s.sl W.l1 c0 W.l1) (hreg : s'.reg = upd2 s.reg W.l1 c0 true)
    (hctm : s'.ctm = upd2 s.ctm W.l1 c0 x) (hn : s'.migNum = s.migNum)
    (hm : s'.msgs = s.msgs) : Shape W s' := by
  refine ⟨fun h c h0 hs => ?_, fun g c g0 gl hs => ?_, fun h c hr => ?_, fun c hr => ?_,
    fun h c hr => ?_, fun i m hm' => ?_⟩
  · rw [hsl, upd2_apply] at hs
    split_ifs at hs with hq
    · obtain ⟨rfl, rfl⟩ := hq; exact hl1
    · exact ih.slSelf h c h0 hs
  · rw [hsl, upd2_apply] at hs
    split_ifs at hs with hq
    · exact absurd hq.1 gl
    · rw [hn]; exact ih.slNum g c g0 gl hs
  · rw [hreg, upd2_apply] at hr
    rw [hreg, upd2_apply]
    split_ifs at hr with hq
    · simp [hq.2]
    · have := ih.regL1 h c hr
      split_ifs <;> simp [this]
  · rw [hreg, upd2_apply] at hr
    split_ifs at hr with hq
    · exact ⟨by rw [hq.2]; exact hc0, by rw [hq.2]; exact hl1⟩
    · exact ih.regL1Id c hr
  · rw [hreg, upd2_apply] at hr
    rw [hctm, upd2_apply]
    split_ifs at hr ⊢ with hq
    · exact hx
    · exact ih.regCtm h c hr
  · rw [hm] at hm'; exact ih.msg i m hm'

/-- A mint keeps the shape. -/
theorem shape_mint {W : World} {s : Sys} {h : ChainId} {i : ℕ} {m : Msg} {fresh : Bool}
    (ih : Shape W s) (ihm : ∀ i m, s.msgs i = some m → s.reg W.l1 m.chain = true)
    (hg : MintOk W s h i m) :
    Shape W (mintPost W s h i m (W.ctmOfAsset h m.asset) fresh) := by
  obtain ⟨_, _, _, _, hcd, hdisj⟩ := ih.msg i m hg.msgAt
  have hregc := ihm i m hg.msgAt
  have hfor := hg.forHub
  refine ⟨fun h' c h0 hs => ?_, fun g c g0 gl hs => ?_, fun h' c hr => ?_, fun c hr => ?_,
    fun h' c hr => ?_, fun j m' hm' => ?_⟩
  · simp only [mintPost, upd2_apply] at hs
    split_ifs at hs with hq
    · obtain ⟨rfl, rfl⟩ := hq; rw [← hfor]; exact hcd
    · exact ih.slSelf h' c h0 hs
  · simp only [mintPost, upd2_apply] at hs ⊢
    split_ifs at hs ⊢ with hq
    · obtain ⟨rfl, rfl⟩ := hq
      rcases hdisj with ⟨_, _, hn⟩ | ⟨hd, _, _⟩
      · exact hn
      · exact absurd (hfor.symm.trans hd) gl
    · exact ih.slNum g c g0 gl hs
  · simp only [mintPost, upd2_apply] at hr ⊢
    split_ifs at hr with hq
    · obtain ⟨rfl, rfl⟩ := hq; split_ifs <;> simp [hregc]
    · have := ih.regL1 h' c hr; split_ifs <;> simp [this]
  · simp only [mintPost, upd2_apply] at hr
    split_ifs at hr with hq
    · obtain ⟨-, rfl⟩ := hq; exact ih.regL1Id _ hregc
    · exact ih.regL1Id c hr
  · simp only [mintPost, upd2_apply] at hr ⊢
    split_ifs at hr ⊢ with hq
    · exact hg.ctmKnown
    · exact ih.regCtm h' c hr
  · simp only [mintPost, upd] at hm'
    split_ifs at hm' with hj
    · cases hm'; exact ih.msg i m hg.msgAt
    · exact ih.msg j m' hm'

/-- A status change keeps the shape of the messages. -/
theorem shape_status {W : World} {s : Sys} {i : ℕ} {m : Msg} {st : MsgStatus}
    (ih : ∀ i m, s.msgs i = some m → MsgShape W m) (hm : s.msgs i = some m) :
    ∀ j m', upd s.msgs i (some { m with status := st }) j = some m' → MsgShape W m' := by
  intro j m' hm'
  simp only [upd] at hm'
  split_ifs at hm' with hj
  · cases hm'; exact ih i m hm
  · exact ih j m' hm'

theorem shape_inv {W : World} (hl : W.l1 ≠ 0) : ∀ s, Reach W s → Shape W s := by
  refine reach_induction _ (fun s hi => ?_) ?_
  · refine ⟨fun h c h0 hs => ?_, fun g c g0 _ hs => ?_, fun h c hr => ?_, fun c hr => ?_,
      fun h c hr => ?_, fun i m hm => ?_⟩
    · rw [hi.sl] at hs; exact absurd hs.symm h0
    · rw [hi.sl] at hs; exact absurd hs.symm g0
    · simp [hi.reg] at hr
    · simp [hi.reg] at hr
    · simp [hi.reg] at hr
    · simp [hi.msgs] at hm
  intro s l s' hr ih hst
  cases hst with
  | @createChain c0 x hg =>
    exact shape_register ih hg.chainNonzero hg.notL1 hg.ctmNonzero rfl rfl rfl rfl rfl
  | @registerDeployed c0 hg =>
    exact shape_register ih hg.chainNonzero hg.notL1 hg.ctmNonzero rfl rfl rfl rfl rfl
  | @burn h c0 t a hg =>
    have htne := hg.dst_ne
    have hc0h : c0 ≠ h := ih.slSelf h c0 hg.hubNonzero hg.settlesHere
    refine ⟨fun h' c h0 hs => ?_, fun g c g0 gl hs => ?_, ih.regL1, ih.regL1Id, ih.regCtm,
      fun i m hm => ?_⟩
    · simp only [burnPost, upd2_apply] at hs
      split_ifs at hs with hq
      · obtain ⟨rfl, rfl⟩ := hq; exact absurd hs htne
      · exact ih.slSelf h' c h0 hs
    · simp only [burnPost, upd2_apply] at hs ⊢
      split_ifs at hs ⊢ with hq
      · obtain ⟨rfl, rfl⟩ := hq; exact absurd hs htne
      · exact ih.slNum g c g0 gl hs
    · simp only [burnPost, upd] at hm
      split_ifs at hm with hi
      · cases hm
        have hct : c0 ≠ t := by
          rintro rfl; have h1 := hg.notSL; rw [hg.dstListed] at h1; cases h1
        refine ⟨hg.hubNonzero, ?_, hg.dstListed, hc0h, hct, ?_⟩
        · by_cases hh : h = W.l1
          · exact (ih.regL1Id t (hh ▸ (hg.dstDiamond (hh ▸ (hg.l1Record hh).1)).1)).1
          · rw [hg.toL1 hh]; exact hl
        · by_cases hh : h = W.l1
          · exact Or.inl ⟨hh, (hg.l1Record hh).1, (hg.l1Record hh).2⟩
          · refine Or.inr ⟨hg.toL1 hh, hh, ?_⟩
            show s.migNum h c0 + 1 = numToL1
            rw [ih.slNum h c0 hg.hubNonzero hh hg.settlesHere]; rfl
      · exact ih.msg i m hm
  | @mintFresh h i m hg =>
    exact shape_mint ih (holder_inv hl s hr).1 hg
  | @mintReturn h i m hg =>
    exact shape_mint ih (holder_inv hl s hr).1 hg
  | @failDeposit j m hm _ _ =>
    exact ⟨ih.slSelf, ih.slNum, ih.regL1, ih.regL1Id, ih.regCtm, shape_status ih.msg hm⟩
  | @confirm j m f hg =>
    have hcs : m.chain ≠ W.l1 := hg.fromL1 ▸ (ih.msg j m hg.msgAt).2.2.2.1
    cases f
    · exact ⟨ih.slSelf, ih.slNum, ih.regL1, ih.regL1Id, ih.regCtm,
        shape_status ih.msg hg.msgAt⟩
    · refine ⟨fun h' c h0 hs => ?_, fun g c g0 gl hs => ?_, ih.regL1, ih.regL1Id, ih.regCtm,
        shape_status ih.msg hg.msgAt⟩
      · simp only [confirmPost, ite_true, upd2_apply] at hs
        split_ifs at hs with hq
        · obtain ⟨rfl, rfl⟩ := hq; exact hcs
        · exact ih.slSelf h' c h0 hs
      · simp only [confirmPost, ite_true, upd2_apply] at hs ⊢
        split_ifs at hs ⊢ with hq
        · exact absurd hq.1 gl
        · exact ih.slNum g c g0 gl hs
  | @setSLChainId h p q h0 _ =>
    refine ⟨ih.slSelf, fun g c g0 gl hs => ?_, ih.regL1, ih.regL1Id, ih.regCtm, ih.msg⟩
    rw [slChainIdPost_migNum (fun hq => ih.slSelf g c g0 hs (hq.2.trans hq.1.symm))]
    exact ih.slNum g c g0 gl hs
  | pauseMigration => exact ⟨ih.slSelf, ih.slNum, ih.regL1, ih.regL1Id, ih.regCtm, ih.msg⟩
  | unpauseMigration => exact ⟨ih.slSelf, ih.slNum, ih.regL1, ih.regL1Id, ih.regCtm, ih.msg⟩
  | pauseCTM => exact ⟨ih.slSelf, ih.slNum, ih.regL1, ih.regL1Id, ih.regCtm, ih.msg⟩
  | unpauseCTM => exact ⟨ih.slSelf, ih.slNum, ih.regL1, ih.regL1Id, ih.regCtm, ih.msg⟩
  | pause => exact ⟨ih.slSelf, ih.slNum, ih.regL1, ih.regL1Id, ih.regCtm, ih.msg⟩
  | unpause => exact ⟨ih.slSelf, ih.slNum, ih.regL1, ih.regL1Id, ih.regCtm, ih.msg⟩
  | ctmUpgrade => exact ⟨ih.slSelf, ih.slNum, ih.regL1, ih.regL1Id, ih.regCtm, ih.msg⟩
  | diamondUpgrade => exact ⟨ih.slSelf, ih.slNum, ih.regL1, ih.regL1Id, ih.regCtm, ih.msg⟩

/-! ## Layer 6: before it reaches a settlement layer, a chain is registered only on L1 -/

/-- Chain `c` is registered on no hub other than L1. -/
def OnlyOnL1 (W : World) (s : Sys) (c : ChainId) : Prop := ∀ g, g ≠ W.l1 → s.reg g c = false

/-- The layer-6 invariant. -/
structure Elsewhere (W : World) (s : Sys) : Prop where
  /-- At L1 number 0 the chain is registered only on L1. -/
  num0 : ∀ c, s.migNum W.l1 c = 0 → OnlyOnL1 W s c
  /-- While a message out of L1 is live, its chain is registered only on L1. -/
  out : ∀ i m, s.msgs i = some m → m.Live → m.src = W.l1 → OnlyOnL1 W s m.chain

/-- A message's number is never 0. -/
theorem MsgShape.num_ne_zero {W : World} {m : Msg} (h : MsgShape W m) : m.num ≠ 0 := by
  rcases h.2.2.2.2.2 with ⟨_, _, hn⟩ | ⟨_, _, hn⟩ <;> rw [hn] <;> decide

/-- A message to a hub other than L1 comes from L1. -/
theorem MsgShape.src_of_dst {W : World} {m : Msg} (h : MsgShape W m) (hd : m.dst ≠ W.l1) :
    m.src = W.l1 := by
  rcases h.2.2.2.2.2 with ⟨hs, _, _⟩ | ⟨hd', _, _⟩
  · exact hs
  · exact absurd hd' hd

/-- A message to L1 carries number 2 and does not come from L1. -/
theorem MsgShape.of_dst_l1 {W : World} {m : Msg} (h : MsgShape W m) (hd : m.dst = W.l1) :
    m.src ≠ W.l1 ∧ m.num = numToL1 := by
  rcases h.2.2.2.2.2 with ⟨_, hd', _⟩ | ⟨_, hs, hn⟩
  · exact absurd hd hd'
  · exact ⟨hs, hn⟩

/-- A message from L1 goes elsewhere and carries number 1. -/
theorem MsgShape.of_src_l1 {W : World} {m : Msg} (h : MsgShape W m) (hs : m.src = W.l1) :
    m.dst ≠ W.l1 ∧ m.num = numToSL := by
  rcases h.2.2.2.2.2 with ⟨_, hd, hn⟩ | ⟨_, hs', _⟩
  · exact ⟨hd, hn⟩
  · exact absurd hs hs'

/-- A consumed or executed message is not live. -/
theorem msg_not_live {m : Msg} {st : MsgStatus} (hst : st = .executed ∨ st = .done) :
    ¬ ({ m with status := st } : Msg).Live := by
  rcases hst with rfl | rfl <;> simp [Msg.Live]

/-- A mint keeps the layer-6 invariant. -/
theorem elsewhere_mint {W : World} {s : Sys} {h : ChainId} {i : ℕ} {m : Msg} {fresh : Bool}
    (hl : W.l1 ≠ 0) (hr : Reach W s) (ih : Elsewhere W s) (hsh : Shape W s)
    (hg : MintOk W s h i m) :
    Elsewhere W (mintPost W s h i m (W.ctmOfAsset h m.asset) fresh) := by
  have hmsg : Holds s m.chain (.msg i) := ⟨m, hg.msgAt, rfl, Or.inl hg.pending⟩
  have hshm := hsh.msg i m hg.msgAt
  refine ⟨fun c hn g hg' => ?_, fun j m' hm' hlv hsrc g hg' => ?_⟩
  · simp only [mintPost, upd2_apply] at hn ⊢
    have hn' : s.migNum W.l1 c = 0 := by
      split_ifs at hn with hq
      · exact absurd hn hshm.num_ne_zero
      · exact hn
    by_cases hq : g = h ∧ c = m.chain
    · obtain ⟨rfl, rfl⟩ := hq
      have hsrcL1 : m.src = W.l1 := hshm.src_of_dst (by rw [hg.forHub]; exact hg')
      have hnd : ND W s m.chain i := ⟨m, hg.msgAt, hsrcL1, rfl, by simp [hg.pending]⟩
      exact absurd hn' ((l1Departure_inv s hr m.chain).2 i hnd).1
    · rw [ite_eq_right hq]; exact ih.num0 c hn' g hg'
  · simp only [mintPost, upd] at hm'
    split_ifs at hm' with hj
    · cases hm'; exact absurd hlv (msg_not_live (Or.inl rfl))
    · simp only [mintPost, upd2_apply]
      by_cases hq : g = h ∧ m'.chain = m.chain
      · have hj' : Holds s m.chain (.msg j) := ⟨m', hm', hq.2, hlv⟩
        have := (holds_unique hl hr hmsg (.msg j)).1 hj'
        simp only [Holder.msg.injEq] at this
        exact absurd this hj
      · rw [ite_eq_right hq]; exact ih.out j m' hm' hlv hsrc g hg'

/-- A status change of message `i` to a live status keeps the `out` field. -/
theorem elsewhere_out_status {W : World} {s : Sys} {i : ℕ} {m : Msg} {st : MsgStatus}
    (ih : Elsewhere W s) (hm : s.msgs i = some m) (hlive : m.Live) :
    ∀ j m', upd s.msgs i (some { m with status := st }) j = some m' → m'.Live →
      m'.src = W.l1 → OnlyOnL1 W { s with msgs := upd s.msgs i (some { m with status := st }) }
        m'.chain := by
  intro j m' hm' hlv hsrc
  simp only [upd] at hm'
  split_ifs at hm' with hj
  · cases hm'; exact ih.out i m hm hlive hsrc
  · exact ih.out j m' hm' hlv hsrc

theorem elsewhere_inv {W : World} (hl : W.l1 ≠ 0) : ∀ s, Reach W s → Elsewhere W s := by
  refine reach_induction _ (fun s hi => ⟨fun c _ g _ => hi.reg g c,
    fun i m hm => by simp [hi.msgs] at hm⟩) ?_
  intro s l s' hr ih hst
  have hsh := shape_inv hl s hr
  cases hst with
  | @createChain c0 x hg =>
    refine ⟨fun c hn g hg' => ?_, fun i m hm hlv hsrc g hg' => ?_⟩
    · simp only [createPost, upd2_apply, hg', false_and, ite_false]; exact ih.num0 c hn g hg'
    · simp only [createPost, upd2_apply, hg', false_and, ite_false]
      exact ih.out i m hm hlv hsrc g hg'
  | @registerDeployed c0 hg =>
    refine ⟨fun c hn g hg' => ?_, fun i m hm hlv hsrc g hg' => ?_⟩
    · simp only [registerDeployedPost, upd2_apply, hg', false_and, ite_false]
      exact ih.num0 c hn g hg'
    · simp only [registerDeployedPost, upd2_apply, hg', false_and, ite_false]
      exact ih.out i m hm hlv hsrc g hg'
  | @burn h c0 t a hg =>
    refine ⟨fun c hn => ?_, fun i m hm hlv hsrc => ?_⟩
    · have hn' : s.migNum W.l1 c = 0 := by
        by_cases hq : W.l1 = h ∧ c = c0
        · have : (burnPost W s h c0 t a).migNum W.l1 c = s.migNum h c0 + 1 := by
            simp only [burnPost, upd2_apply, ite_eq_left hq]
          omega
        · have : (burnPost W s h c0 t a).migNum W.l1 c = s.migNum W.l1 c := by
            simp only [burnPost, upd2_apply, ite_eq_right hq]
          omega
      exact ih.num0 c hn'
    · simp only [burnPost, upd] at hm
      split_ifs at hm with hi
      · cases hm
        have hh : h = W.l1 := hsrc
        have hn0 : s.migNum W.l1 c0 = 0 := by
          have := (hg.l1Record hh).2; rw [hh] at this; simp [numToSL] at this; exact this
        exact ih.num0 c0 hn0
      · exact ih.out i m hm hlv hsrc
  | @mintFresh h i m hg =>
    exact elsewhere_mint hl hr ih hsh hg
  | @mintReturn h i m hg =>
    exact elsewhere_mint hl hr ih hsh hg
  | @failDeposit j m hm hpend _ =>
    exact ⟨ih.num0, elsewhere_out_status ih hm (Or.inl hpend)⟩
  | @confirm j m f hg =>
    have hoff : ∀ j' m', (confirmPost W s j m f).msgs j' = some m' → m'.Live →
        m'.src = W.l1 → OnlyOnL1 W s m'.chain := by
      intro j' m' hm' hlv hsrc
      have hm'' : upd s.msgs j (some { m with status := .done }) j' = some m' := by
        cases f <;> exact hm'
      simp only [upd] at hm''
      split_ifs at hm'' with hj
      · cases hm''; exact absurd hlv (msg_not_live (Or.inr rfl))
      · exact ih.out j' m' hm'' hlv hsrc
    cases f
    · exact ⟨ih.num0, hoff⟩
    · refine ⟨fun c hn => ?_, hoff⟩
      simp only [confirmPost, ite_true, upd2_apply] at hn
      split_ifs at hn with hq
      · obtain ⟨-, rfl⟩ := hq
        exact ih.out j m hg.msgAt (Or.inr (hg.failed rfl)) hg.fromL1
      · exact ih.num0 c hn
  | @setSLChainId h p q _ hl2 =>
    refine ⟨fun c hn => ih.num0 c ?_, ih.out⟩
    rwa [slChainIdPost_migNum (fun hq => hl2 hq.1.symm)] at hn
  | pauseMigration => exact ⟨ih.num0, ih.out⟩
  | unpauseMigration => exact ⟨ih.num0, ih.out⟩
  | pauseCTM => exact ⟨ih.num0, ih.out⟩
  | unpauseCTM => exact ⟨ih.num0, ih.out⟩
  | pause => exact ⟨ih.num0, ih.out⟩
  | unpause => exact ⟨ih.num0, ih.out⟩
  | ctmUpgrade => exact ⟨ih.num0, ih.out⟩
  | diamondUpgrade => exact ⟨ih.num0, ih.out⟩


/-! ## Layer 7: L1's bridgehub view of a chain -/

/-- The layer-7 invariant. -/
structure L1View (W : World) (s : Sys) : Prop where
  /-- A hub other than L1 that holds the chain is what L1's bridgehub records. -/
  hub : ∀ c g, g ≠ W.l1 → Holds s c (.hub g) → s.sl W.l1 c = g
  /-- A live message's endpoint other than L1 is what L1's bridgehub records. -/
  msg : ∀ i m, s.msgs i = some m → m.Live →
    s.sl W.l1 m.chain = if m.src = W.l1 then m.dst else m.src

/-- A mint keeps L1's view. -/
theorem l1View_mint {W : World} {s : Sys} {h : ChainId} {i : ℕ} {m : Msg} {fresh : Bool}
    (hl : W.l1 ≠ 0) (hr : Reach W s) (ih : L1View W s) (hsh : Shape W s)
    (hg : MintOk W s h i m)
    (hr' : Reach W (mintPost W s h i m (W.ctmOfAsset h m.asset) fresh)) :
    L1View W (mintPost W s h i m (W.ctmOfAsset h m.asset) fresh) := by
  have hmsg : Holds s m.chain (.msg i) := ⟨m, hg.msgAt, rfl, Or.inl hg.pending⟩
  have hpost : Holds (mintPost W s h i m (W.ctmOfAsset h m.asset) fresh) m.chain (.hub h) :=
    ⟨hg.hubNonzero, by simp [mintPost, upd2_apply]⟩
  have hshm := hsh.msg i m hg.msgAt
  refine ⟨fun c g hg' hh => ?_, fun j m' hm' hlv => ?_⟩
  · by_cases hc : c = m.chain
    · subst hc
      have := (holds_unique hl hr' hpost (.hub g)).1 hh
      simp only [Holder.hub.injEq] at this
      subst this
      have hsrc : m.src = W.l1 := hshm.src_of_dst (by rw [hg.forHub]; exact hg')
      have hv := ih.msg i m hg.msgAt (Or.inl hg.pending)
      rw [ite_eq_left hsrc, hg.forHub] at hv
      simpa [mintPost, upd2_apply, Ne.symm hg'] using hv
    · have hh' : Holds s c (.hub g) := by simpa [Holds, mintPost, upd2_apply, hc] using hh
      have := ih.hub c g hg' hh'
      simpa [mintPost, upd2_apply, hc] using this
  · simp only [mintPost, upd] at hm'
    split_ifs at hm' with hj
    · cases hm'; exact absurd hlv (msg_not_live (Or.inl rfl))
    · by_cases hc : m'.chain = m.chain
      · have hj' : Holds s m.chain (.msg j) := ⟨m', hm', hc, hlv⟩
        have := (holds_unique hl hr hmsg (.msg j)).1 hj'
        simp only [Holder.msg.injEq] at this; exact absurd this hj
      · have := ih.msg j m' hm' hlv
        simpa [mintPost, upd2_apply, hc] using this

theorem l1View_inv {W : World} (hl : W.l1 ≠ 0) : ∀ s, Reach W s → L1View W s := by
  refine reach_induction _ (fun s hi => ⟨fun c g _ hh => ?_,
    fun i m hm => by simp [hi.msgs] at hm⟩) ?_
  · exact absurd (hh.2.symm.trans (hi.sl g c)) hh.1
  intro s l s' hr ih hst
  have hsh := shape_inv hl s hr
  have hr' : Reach W s' := Reach.step hr hst
  cases hst with
  | @createChain c0 x hg =>
    have hpost : Holds (createPost W s c0 x) c0 (.hub W.l1) :=
      ⟨hl, by simp [createPost, upd2_apply]⟩
    have hno := ((holder_inv hl s hr).2 c0).2 hg.notRegistered
    refine ⟨fun c g hg' hh => ?_, fun i m hm hlv => ?_⟩
    · by_cases hc : c = c0
      · subst hc
        have := (holds_unique hl hr' hpost (.hub g)).1 hh
        simp only [Holder.hub.injEq] at this; exact absurd this hg'
      · have hh' : Holds s c (.hub g) := by simpa [Holds, createPost, upd2_apply, hc] using hh
        have := ih.hub c g hg' hh'
        simpa [createPost, upd2_apply, hc] using this
    · have hm' : s.msgs i = some m := hm
      by_cases hc : m.chain = c0
      · exact absurd ⟨m, hm', hc, hlv⟩ (hno (.msg i))
      · have := ih.msg i m hm' hlv
        simpa [createPost, upd2_apply, hc] using this
  | @registerDeployed c0 hg =>
    have hpost : Holds (registerDeployedPost W s c0) c0 (.hub W.l1) :=
      ⟨hl, by simp [registerDeployedPost, upd2_apply]⟩
    have hno := ((holder_inv hl s hr).2 c0).2 hg.notRegistered
    refine ⟨fun c g hg' hh => ?_, fun i m hm hlv => ?_⟩
    · by_cases hc : c = c0
      · subst hc
        have := (holds_unique hl hr' hpost (.hub g)).1 hh
        simp only [Holder.hub.injEq] at this; exact absurd this hg'
      · have hh' : Holds s c (.hub g) := by
          simpa [Holds, registerDeployedPost, upd2_apply, hc] using hh
        have := ih.hub c g hg' hh'
        simpa [registerDeployedPost, upd2_apply, hc] using this
    · have hm' : s.msgs i = some m := hm
      by_cases hc : m.chain = c0
      · exact absurd ⟨m, hm', hc, hlv⟩ (hno (.msg i))
      · have := ih.msg i m hm' hlv
        simpa [registerDeployedPost, upd2_apply, hc] using this
  | @burn h c0 t a hg =>
    have hhub : Holds s c0 (.hub h) := ⟨hg.hubNonzero, hg.settlesHere⟩
    have hpost : Holds (burnPost W s h c0 t a) c0 (.msg s.nMsgs) :=
      ⟨burnMsg s h c0 t a, by simp [burnPost], rfl, Or.inl rfl⟩
    refine ⟨fun c g hg' hh => ?_, fun i m hm hlv => ?_⟩
    · by_cases hc : c = c0
      · subst hc
        have := (holds_unique hl hr' hpost (.hub g)).1 hh
        cases this
      · have hh' : Holds s c (.hub g) := by simpa [Holds, burnPost, upd2_apply, hc] using hh
        have := ih.hub c g hg' hh'
        simpa [burnPost, upd2_apply, hc] using this
    · simp only [burnPost, upd] at hm
      split_ifs at hm with hi
      · cases hm
        simp only [burnPost, upd2_apply, burnMsg]
        by_cases hh : h = W.l1
        · simp [hh]
        · have := ih.hub c0 h hh hhub
          simp [hh, Ne.symm hh, this]
      · by_cases hc : m.chain = c0
        · have hmh : Holds s c0 (.msg i) := ⟨m, hm, hc, hlv⟩
          have := (holds_unique hl hr hhub (.msg i)).1 hmh
          cases this
        · have := ih.msg i m hm hlv
          simpa [burnPost, upd2_apply, hc] using this
  | @mintFresh h i m hg =>
    exact l1View_mint hl hr ih hsh hg hr'
  | @mintReturn h i m hg =>
    exact l1View_mint hl hr ih hsh hg hr'
  | @failDeposit j m hm hpend _ =>
    refine ⟨ih.hub, fun i m' hm' hlv => ?_⟩
    simp only [upd] at hm'
    split_ifs at hm' with hi
    · cases hm'; exact ih.msg j m hm (Or.inl hpend)
    · exact ih.msg i m' hm' hlv
  | @confirm j m f hg =>
    have hm := hg.msgAt
    cases f
    · refine ⟨ih.hub, fun i m' hm' hlv => ?_⟩
      have hm'' : upd s.msgs j (some { m with status := .done }) i = some m' := hm'
      simp only [upd] at hm''
      split_ifs at hm'' with hi
      · cases hm''; exact absurd hlv (msg_not_live (Or.inr rfl))
      · exact ih.msg i m' hm'' hlv
    · have hfl := hg.failed rfl
      have hmsg : Holds s m.chain (.msg j) := ⟨m, hm, rfl, Or.inr hfl⟩
      have hpost : Holds (confirmPost W s j m true) m.chain (.hub W.l1) :=
        ⟨hl, by simp [confirmPost, upd2_apply]⟩
      refine ⟨fun c g hg' hh => ?_, fun i m' hm' hlv => ?_⟩
      · by_cases hc : c = m.chain
        · subst hc
          have := (holds_unique hl hr' hpost (.hub g)).1 hh
          simp only [Holder.hub.injEq] at this; exact absurd this hg'
        · have hh' : Holds s c (.hub g) := by
            simpa [Holds, confirmPost, upd2_apply, hc] using hh
          have := ih.hub c g hg' hh'
          simpa [confirmPost, upd2_apply, hc] using this
      · have hm'' : upd s.msgs j (some { m with status := .done }) i = some m' := hm'
        simp only [upd] at hm''
        split_ifs at hm'' with hi
        · cases hm''; exact absurd hlv (msg_not_live (Or.inr rfl))
        · by_cases hc : m'.chain = m.chain
          · have hj' : Holds s m.chain (.msg i) := ⟨m', hm'', hc, hlv⟩
            have := (holds_unique hl hr hmsg (.msg i)).1 hj'
            simp only [Holder.msg.injEq] at this; exact absurd this hi
          · have := ih.msg i m' hm'' hlv
            simpa [confirmPost, upd2_apply, hc] using this
  | setSLChainId => exact ⟨ih.hub, ih.msg⟩
  | pauseMigration => exact ⟨ih.hub, ih.msg⟩
  | unpauseMigration => exact ⟨ih.hub, ih.msg⟩
  | pauseCTM => exact ⟨ih.hub, ih.msg⟩
  | unpauseCTM => exact ⟨ih.hub, ih.msg⟩
  | pause => exact ⟨ih.hub, ih.msg⟩
  | unpause => exact ⟨ih.hub, ih.msg⟩
  | ctmUpgrade => exact ⟨ih.hub, ih.msg⟩
  | diamondUpgrade => exact ⟨ih.hub, ih.msg⟩

/-! ## Messages, L1's view, and enabledness -/

theorem MessagesRunBetweenL1AndALayer : Properties.MessagesRunBetweenL1AndALayer := by
  intro W s hl hr i m hm
  exact (shape_inv hl s hr).msg i m hm

theorem L1SettlementLayerTracksHolder : Properties.L1SettlementLayerTracksHolder := by
  intro W s hl hr c
  have hv := l1View_inv hl s hr
  refine ⟨fun g hg hh => hv.hub c g hg hh, fun i m hm hc hlv => ?_⟩
  rw [← hc]; exact hv.msg i m hm hlv

/-- While a live message holds a chain, the chain is registered on L1, L1's number of it is 1
with interval 1 active, L1's bridgehub records another hub, and L1's diamond of it is away. -/
theorem in_flight_l1 {W : World} {s : Sys} {i : ℕ} {m : Msg} (hl : W.l1 ≠ 0) (hr : Reach W s)
    (hm : s.msgs i = some m) (hlv : m.Live) :
    s.reg W.l1 m.chain = true ∧ s.migNum W.l1 m.chain = numToSL ∧ s.ivActive m.chain = true ∧
      s.sl W.l1 m.chain ≠ W.l1 ∧ s.away W.l1 m.chain = true := by
  have hmsg : Holds s m.chain (.msg i) := ⟨m, hm, rfl, hlv⟩
  have hreg : s.reg W.l1 m.chain = true := (holder_inv hl s hr).1 i m hm
  have hnotL1 : ¬ Holds s m.chain (.hub W.l1) := fun h => by
    have := (holds_unique hl hr hmsg (.hub W.l1)).1 h; cases this
  have hbook := L1MigrationBookkeeping W s hl hr m.chain
  have hn1 : s.migNum W.l1 m.chain = numToSL := by
    by_contra hne; exact hnotL1 ((hbook.2.2.2.2.2.2 hreg).2 hne)
  have hsl : s.sl W.l1 m.chain ≠ W.l1 := fun h => hnotL1 ⟨hl, h⟩
  have haway : s.away W.l1 m.chain = true := by
    have hiff := ((diamondAgree_inv hl s hr W.l1 m.chain).1 hreg).2
    cases hb : s.away W.l1 m.chain
    · exact absurd (hiff.2 hb) hsl
    · rfl
  exact ⟨hreg, hn1, (hbook.2.2.2.2.1 hn1).1, hsl, haway⟩

theorem GatewayAcceptsArrival : Properties.GatewayAcceptsArrival := by
  intro W s i m hl hr hm hpend hsrc hen hp heco hctm hknown hpv
  have hshm := (shape_inv hl s hr).msg i m hm
  have hdl1 : m.dst ≠ W.l1 := (hshm.of_src_l1 hsrc).1
  have hd0 : m.dst ≠ 0 := hshm.2.1
  have hmsg : Holds s m.chain (.msg i) := ⟨m, hm, rfl, Or.inl hpend⟩
  have hnreg : s.reg m.dst m.chain = false :=
    (elsewhere_inv hl s hr).out i m hm (Or.inl hpend) hsrc m.dst hdl1
  have hnot : s.sl m.dst m.chain ≠ m.dst := by
    intro h
    have := (holds_unique hl hr hmsg (.hub m.dst)).1 ⟨hd0, h⟩
    cases this
  have hok : MintOk W s m.dst i m :=
    { msgAt := hm, pending := hpend, forHub := rfl, hubNonzero := hd0, notPaused := hp
      enabled := hen, ecoOff := heco, ctmOff := hctm
      l1Numbers := fun h => absurd h hdl1, l1Interval := fun h => absurd h hdl1
      ctmKnown := hknown, notHere := hnot }
  have hst := Step.mintFresh hok hnreg hpv hdl1
  refine ⟨hnreg, _, hst, ?_⟩
  exact holds_unique hl (Reach.step hr hst) ⟨hd0, by simp [mintPost, upd2_apply]⟩

theorem L1AcceptsReturn : Properties.L1AcceptsReturn := by
  intro W s i m hl hr hm hpend hdst hen hp heco hctm hknown hdpv
  have hshm := (shape_inv hl s hr).msg i m hm
  have hnum : m.num = numToL1 := (hshm.of_dst_l1 hdst).2
  obtain ⟨hreg, hn1, hiv, hsl, haway⟩ := in_flight_l1 hl hr hm (Or.inl hpend)
  have hok : MintOk W s W.l1 i m :=
    { msgAt := hm, pending := hpend, forHub := hdst, hubNonzero := hl, notPaused := hp
      enabled := hen, ecoOff := heco, ctmOff := hctm
      l1Numbers := fun _ => ⟨hn1, hnum⟩, l1Interval := fun _ => hiv
      ctmKnown := hknown, notHere := hsl }
  have hst := Step.mintReturn hok hreg hdpv haway
  refine ⟨_, hst, by simp [mintPost, upd2_apply, hnum], ?_⟩
  exact holds_unique hl (Reach.step hr hst) ⟨hl, by simp [mintPost, upd2_apply]⟩

theorem FailedDepositConfirmable : Properties.FailedDepositConfirmable := by
  intro W s i m hl hr hm hsrc hfl hpv
  obtain ⟨hreg, hn1, _, _, haway⟩ := in_flight_l1 hl hr hm (Or.inr hfl)
  have hok : ConfirmOk W s i m true :=
    { msgAt := hm, fromL1 := hsrc, failed := fun _ => hfl, executed := fun h => by cases h
      registered := hreg, ctmSet := (shape_inv hl s hr).regCtm W.l1 m.chain hreg
      failNum := fun _ => hn1, failAway := fun _ => haway, failPv := fun _ => hpv }
  have hst := Step.confirm hok
  refine ⟨_, hst, holds_unique hl (Reach.step hr hst) ⟨hl, by simp [confirmPost, upd2_apply]⟩,
    ?_, ?_⟩
  · simp [confirmPost, upd2_apply, hn1, numToSL]
  · simp [confirmPost, upd]


/-! ## Witnesses

Concrete states of `cahWorld`, named after what happened last; each step's guards are checked
by evaluation. -/

theorem cahInit_init : Init cahInit :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ _ => rfl, fun _ => rfl, rfl⟩

/-- After L1's `createNewChain(2, 7)` (the gateway). -/
def cahStGateway : Sys := createPost cahWorld cahInit 2 7
/-- After the setup (chain `3` created too). -/
def cahStSetup : Sys := createPost cahWorld cahStGateway 3 7
/-- The message of L1's burn of chain `3` to the gateway. -/
def cahMsgOut : Msg := burnMsg cahStSetup 1 3 2 5
/-- After L1's burn of chain `3` to the gateway. -/
def cahStOut : Sys := burnPost cahWorld cahStSetup 1 3 2 5
/-- After the gateway's fresh mint of message `0`. -/
def cahStOnGw : Sys :=
  mintPost cahWorld cahStOut 2 0 cahMsgOut (cahWorld.ctmOfAsset 2 cahMsgOut.asset) true
/-- After L1 confirms the deposit's success. -/
def cahStConfirmed : Sys :=
  confirmPost cahWorld cahStOnGw 0 { cahMsgOut with status := .executed } false
/-- The message of the gateway's burn of chain `3` back to L1. -/
def cahMsgBack : Msg := burnMsg cahStConfirmed 2 3 1 5
/-- After the gateway's burn back. -/
def cahStBack : Sys := burnPost cahWorld cahStConfirmed 2 3 1 5
/-- After L1's returning mint of message `1`. -/
def cahStReturned : Sys :=
  mintPost cahWorld cahStBack 1 1 cahMsgBack (cahWorld.ctmOfAsset 1 cahMsgBack.asset) false

theorem cah_create_gw : Step cahWorld cahInit (.createChain 2 7) cahStGateway :=
  Step.createChain ⟨by decide, by decide, by decide, by decide, rfl, rfl⟩

theorem cah_create_chain : Step cahWorld cahStGateway (.createChain 3 7) cahStSetup :=
  Step.createChain ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem cah_burn_out : Step cahWorld cahStSetup (.burn 1 3 2 5) cahStOut :=
  Step.burn (by constructor <;> decide)

theorem cah_mint_gw : Step cahWorld cahStOut (.mint 2 0 3 5) cahStOnGw :=
  Step.mintFresh (m := cahMsgOut) (by constructor <;> first | rfl | decide) (by decide)
    (by decide) (by decide)

theorem cah_confirm_ok : Step cahWorld cahStOnGw (.confirm 0 3 false) cahStConfirmed :=
  Step.confirm (m := { cahMsgOut with status := .executed })
    (by constructor <;> first | rfl | decide)

theorem cah_burn_back : Step cahWorld cahStConfirmed (.burn 2 3 1 5) cahStBack :=
  Step.burn (by constructor <;> decide)

theorem cah_mint_l1 : Step cahWorld cahStBack (.mint 1 1 3 5) cahStReturned :=
  Step.mintReturn (m := cahMsgBack) (by constructor <;> first | rfl | decide) (by decide)
    (by decide) (by decide)

theorem cah_run_setup : Run cahWorld cahInit cahSetup cahStSetup :=
  .cons cah_create_gw (.cons cah_create_chain .nil)

theorem cah_run_roundTrip : Run cahWorld cahInit cahRoundTrip cahStReturned :=
  .cons cah_create_gw (.cons cah_create_chain (.cons cah_burn_out (.cons cah_mint_gw
    (.cons cah_confirm_ok (.cons cah_burn_back (.cons cah_mint_l1 .nil))))))

theorem CahRoundTripWitness : Properties.CahRoundTripWitness := by
  have hr := cah_run_roundTrip.reach (.init cahInit_init)
  refine ⟨cahInit_init, by decide, cahStReturned, cah_run_roundTrip, hr, by decide, by decide,
    by decide, by decide, ?_⟩
  exact holds_unique (by decide) hr ⟨by decide, by decide⟩

theorem CahInFlightWitness : Properties.CahInFlightWitness := by
  have hrun : Run cahWorld cahInit (cahSetup ++ [.burn 1 3 2 5]) cahStOut :=
    .cons cah_create_gw (.cons cah_create_chain (.cons cah_burn_out .nil))
  have hr := hrun.reach (.init cahInit_init)
  refine ⟨cahStOut, hrun, hr, by decide, ?_, by decide, by decide, by decide, by decide, by decide,
    by decide⟩
  exact holds_unique (by decide) hr ⟨cahMsgOut, rfl, rfl, Or.inl rfl⟩

theorem CahGatewayWitness : Properties.CahGatewayWitness := by
  have hrun : Run cahWorld cahInit (cahSetup ++ [.burn 1 3 2 5, .mint 2 0 3 5]) cahStOnGw :=
    .cons cah_create_gw (.cons cah_create_chain (.cons cah_burn_out (.cons cah_mint_gw .nil)))
  have hr := hrun.reach (.init cahInit_init)
  refine ⟨cahStOnGw, hrun, hr, by decide, ?_, by decide, by decide, by decide, by decide,
    by decide⟩
  exact holds_unique (by decide) hr ⟨by decide, by decide⟩

/-- After the deposit of message `0` fails. -/
def cahStFailed : Sys :=
  { cahStOut with msgs := upd cahStOut.msgs 0 (some { cahMsgOut with status := .failed }) }
/-- After L1 confirms the failure. -/
def cahStRecovered : Sys :=
  confirmPost cahWorld cahStFailed 0 { cahMsgOut with status := .failed } true

theorem CahFailedAttemptWitness : Properties.CahFailedAttemptWitness := by
  have hfail : Step cahWorld cahStOut (.failDeposit 0) cahStFailed :=
    Step.failDeposit (m := cahMsgOut) rfl rfl rfl
  have hconf : Step cahWorld cahStFailed (.confirm 0 3 true) cahStRecovered :=
    Step.confirm (m := { cahMsgOut with status := .failed })
      (by constructor <;> first | rfl | decide)
  have hrun : Run cahWorld cahInit cahFailedAttempt cahStRecovered :=
    .cons cah_create_gw (.cons cah_create_chain (.cons cah_burn_out (.cons hfail
      (.cons hconf .nil))))
  refine ⟨cahStSetup, cahStOut, cah_run_setup, cah_run_setup.reach (.init cahInit_init),
    cah_burn_out, cahStRecovered, hrun, by decide, by decide, by decide, _,
    Step.burn (by constructor <;> decide)⟩

theorem CahReturnedChainWitness : Properties.CahReturnedChainWitness := by
  refine ⟨cahStReturned, _, cah_run_roundTrip, cah_run_roundTrip.reach (.init cahInit_init),
    by decide, .cons (Step.ctmUpgrade (by decide)) (.cons (Step.diamondUpgrade (by decide))
      (.cons (Step.pauseMigration rfl) .nil)), ?_⟩
  rintro ⟨s'', hst⟩
  obtain ⟨hg, -⟩ := burn_inv hst
  exact absurd hg.belowMax (by decide)

/-- After the setup with `CHAIN_MIGRATIONS_ENABLED = false`. -/
def cahStSetupDisabled : Sys :=
  createPost cahWorldDisabled (createPost cahWorldDisabled cahInit 2 7) 3 7

theorem CahDisabledWitness : Properties.CahDisabledWitness := by
  have hrun : Run cahWorldDisabled cahInit cahSetup cahStSetupDisabled :=
    .cons (Step.createChain ⟨by decide, by decide, by decide, by decide, rfl, rfl⟩)
      (.cons (Step.createChain ⟨by decide, by decide, by decide, by decide, by decide,
        by decide⟩) .nil)
  refine ⟨rfl, by decide, cahStSetupDisabled, hrun, hrun.reach (.init cahInit_init), by decide,
    ?_, _, Step.burn (by constructor <;> decide)⟩
  rintro ⟨s', hst⟩
  obtain ⟨hg, -⟩ := burn_inv hst
  exact absurd hg.enabled (by decide)

/-- After L1's burn of chain `3` and L1's `pause()`. -/
def cahStOutPaused : Sys := { cahStOut with paused := upd cahStOut.paused 1 true }

theorem CahArrivalWitness : Properties.CahArrivalWitness := by
  have hpause : Step cahWorld cahStOut (.pause 1 10) cahStOutPaused :=
    Step.pause rfl (by decide)
  have hrun : Run cahWorld cahInit (cahSetup ++ [.burn 1 3 2 5, .pause 1 10]) cahStOutPaused :=
    .cons cah_create_gw (.cons cah_create_chain (.cons cah_burn_out (.cons hpause .nil)))
  refine ⟨by decide, rfl, cahStOutPaused, hrun, hrun.reach (.init cahInit_init), by decide,
    by decide,
    ⟨cahMsgOut, rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl, by decide⟩, by decide, by decide,
    by decide, by decide, by decide, _,
    Step.mintFresh (m := cahMsgOut) (by constructor <;> first | rfl | decide) (by decide)
      (by decide) (by decide)⟩

/-- On the way back: L1's CTM `7` moves to version `2`. -/
def cahStBackCtm : Sys := { cahStBack with ctmPV := upd2 cahStBack.ctmPV 1 7 2 }
/-- …the gateway chain's L1 diamond is upgraded to `2`. -/
def cahStBackGwUp : Sys := { cahStBackCtm with dpv := upd2 cahStBackCtm.dpv 1 2 2 }
/-- …and chain `3`'s away L1 diamond is upgraded to `2`. -/
def cahStBackUp : Sys := { cahStBackGwUp with dpv := upd2 cahStBackGwUp.dpv 1 3 2 }

theorem CahReturnInFlightWitness : Properties.CahReturnInFlightWitness := by
  have h1 : Step cahWorld cahStBack (.ctmUpgrade 1 7 2) cahStBackCtm :=
    Step.ctmUpgrade (by decide)
  have h2 : Step cahWorld cahStBackCtm (.diamondUpgrade 1 2 2) cahStBackGwUp :=
    Step.diamondUpgrade (by decide)
  have h3 : Step cahWorld cahStBackGwUp (.diamondUpgrade 1 3 2) cahStBackUp :=
    Step.diamondUpgrade (by decide)
  have hrun : Run cahWorld cahInit
      (cahSetup ++ [.burn 1 3 2 5, .mint 2 0 3 5, .confirm 0 3 false, .burn 2 3 1 5,
        .ctmUpgrade 1 7 2, .diamondUpgrade 1 2 2, .diamondUpgrade 1 3 2]) cahStBackUp :=
    .cons cah_create_gw (.cons cah_create_chain (.cons cah_burn_out (.cons cah_mint_gw
      (.cons cah_confirm_ok (.cons cah_burn_back (.cons h1 (.cons h2 (.cons h3 .nil))))))))
  have hr := hrun.reach (.init cahInit_init)
  refine ⟨by decide, rfl, cahStBackUp, hrun, hr,
    holds_unique (by decide) hr ⟨cahMsgBack, rfl, rfl, Or.inl rfl⟩,
    by decide, ⟨{ { cahMsgOut with status := .executed } with status := .done }, rfl, rfl, rfl,
      rfl, rfl⟩, ⟨cahMsgBack, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl⟩, by decide,
    by decide, by decide, by decide, by decide, by decide, _,
    Step.mintReturn (m := cahMsgBack) (by constructor <;> first | rfl | decide) (by decide)
      (by decide) (by decide)⟩

/-- After L1's burn of chain `3`, an upgrade of L1's CTM `7` to version `2`… -/
def cahStRecCtm : Sys := { cahStOut with ctmPV := upd2 cahStOut.ctmPV 1 7 2 }
/-- …L1's `pause()`… -/
def cahStRecPaused : Sys := { cahStRecCtm with paused := upd cahStRecCtm.paused 1 true }
/-- …and the deposit's failure. -/
def cahStRecFailed : Sys :=
  { cahStRecPaused with
    msgs := upd cahStRecPaused.msgs 0 (some { cahMsgOut with status := .failed }) }

theorem CahRecoveryWitness : Properties.CahRecoveryWitness := by
  have h1 : Step cahWorld cahStOut (.ctmUpgrade 1 7 2) cahStRecCtm := Step.ctmUpgrade (by decide)
  have h2 : Step cahWorld cahStRecCtm (.pause 1 10) cahStRecPaused := Step.pause rfl (by decide)
  have h3 : Step cahWorld cahStRecPaused (.failDeposit 0) cahStRecFailed :=
    Step.failDeposit (m := cahMsgOut) rfl rfl rfl
  have hrun : Run cahWorld cahInit
      (cahSetup ++ [.burn 1 3 2 5, .ctmUpgrade 1 7 2, .pause 1 10, .failDeposit 0])
      cahStRecFailed :=
    .cons cah_create_gw (.cons cah_create_chain (.cons cah_burn_out (.cons h1 (.cons h2
      (.cons h3 .nil)))))
  refine ⟨by decide, cahStRecFailed, hrun, hrun.reach (.init cahInit_init),
    ⟨{ cahMsgOut with status := .failed }, rfl, rfl, rfl, rfl, by decide, by decide⟩, by decide,
    _, Step.confirm (m := { cahMsgOut with status := .failed })
      (by constructor <;> first | rfl | decide)⟩

end Contracts.ChainAssetHandler
