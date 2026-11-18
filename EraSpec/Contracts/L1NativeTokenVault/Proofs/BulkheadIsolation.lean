import EraSpec.Contracts.L1NativeTokenVault.Properties.BulkheadIsolation
import EraSpec.Contracts.L1NativeTokenVault.Proofs.BulkheadIsolationSteps

/-!
# Proofs: what one chain can release from the L1 vault under the v35 per-chain cap

Proofs of `EraSpec.Contracts.L1NativeTokenVault.Properties.BulkheadIsolation`.

The release bounds come from two one-call facts (`Proofs/BulkheadIsolationSteps.lean`): a call
adds to `withdrawn[k][a]` exactly what it counts under `k` (`capStep_withdrawn_eq`), and under a
non-pending key `withdrawn` ends at most at the larger of its old value and
`deposited + backfill` (`capStep_withdrawn_le`), while `deposited` and `backfill` never decrease.
Along a run the second gives `withdrawn ≤ max (start withdrawn) (end deposited + backfill)`.

The ledger identity is the invariance of `capPotential`, `bridgedOut + Σ φ - (pool deposited -
pool withdrawn)`, where `φ` of a chain is `withdrawn - deposited` until its balance moves and
`max backfill (withdrawn - deposited)` after: every call changes it by exactly the legacy amount it
populates.  The concrete countermodels and witnesses run on the deployed constants and are
evaluated by `decide`.
-/

namespace Contracts.L1NativeTokenVault.Bulkhead

open Finset

/-! ## Facts from the invariant -/

theorem CapWF.l1_not_interop {cfg : CapConfig} {s : CapState} (hw : CapWF cfg s) :
    s.interop cfg.l1 = false := by
  cases h : s.interop cfg.l1
  · rfl
  · exact absurd rfl (hw.registered_valid _ (hw.interop_registered _ h)).2.2

theorem CapWF.zero_not_interop {cfg : CapConfig} {s : CapState} (hw : CapWF cfg s) :
    s.interop 0 = false := by
  cases h : s.interop 0
  · rfl
  · exact absurd rfl (hw.registered_valid _ (hw.interop_registered _ h)).1

theorem CapWF.ne_pool {cfg : CapConfig} {s : CapState} (hok : cfg.Ok) (hw : CapWF cfg s) {c : ℕ}
    (hc : s.registered c = true) : c ≠ cfg.pool := by
  have := (hw.registered_valid c hc).2.1
  have := hok.2.1
  omega

theorem CapWF.not_inPool {cfg : CapConfig} {s : CapState} (hw : CapWF cfg s) {c a : ℕ}
    (hc : s.interop c = false) : s.inPool c a = false := by
  cases h : s.inPool c a
  · rfl
  · simp [hw.inPool_interop c a h] at hc

/-- **The invariant is preserved by every call.** -/
theorem capStep_wf {cfg : CapConfig} {l : CapLabel} {s t : CapState}
    (hw : CapWF cfg s) (h : capStep cfg l s = some t) : CapWF cfg t := by
  cases l with
  | toChain c a x =>
    obtain ⟨⟨-, -, hbo, hdep⟩, rfl⟩ := capStep_toChain.mp h
    refine { hw with deposited_lt := ?_, bridgedOut_lt := ?_ }
    · intro k a'
      simp only [toChainPost, capBump_apply]
      split_ifs with hk
      · obtain ⟨hk1, rfl⟩ := hk; exact hdep k hk1
      · simpa using hw.deposited_lt k a'
    · intro a'
      simp only [toChainPost]
      split_ifs with ho
      · simp only [Function.update_apply]
        split_ifs with ha
        · subst ha; exact hbo ho
        · exact hw.bridgedOut_lt a'
      · exact hw.bridgedOut_lt a'
  | fromChain c a x =>
    obtain ⟨⟨-, -, -, hwd⟩, rfl⟩ := capStep_fromChain.mp h
    refine { hw with withdrawn_lt := ?_, bridgedOut_lt := ?_ }
    · intro k a'
      simp only [fromChainPost, capBump_apply]
      split_ifs with hk
      · obtain ⟨hk1, rfl⟩ := hk; exact (hwd k hk1).1
      · simpa using hw.withdrawn_lt k a'
    · intro a'
      simp only [fromChainPost]
      split_ifs with ho
      · simp only [Function.update_apply]
        split_ifs with ha
        · subst ha; have := hw.bridgedOut_lt a'; omega
        · exact hw.bridgedOut_lt a'
      · exact hw.bridgedOut_lt a'
  | setBackfill c a v =>
    obtain ⟨⟨hcp, hv, -, hcred⟩, rfl⟩ := capStep_setBackfill.mp h
    refine { hw with pool_backfill_zero := ?_, deposited_lt := ?_, backfill_lt := ?_ }
    · intro a'
      simp only [setBackfillPost, capUpd2_apply]
      split_ifs with hk
      · exact absurd hk.1.symm hcp
      · exact hw.pool_backfill_zero a'
    · intro k a'
      simp only [setBackfillPost]
      split_ifs with hp
      · simp only [capUpd2_apply]
        split_ifs with hk
        · obtain ⟨rfl, rfl⟩ := hk; exact (hcred hp).2
        · exact hw.deposited_lt k a'
      · exact hw.deposited_lt k a'
    · intro k a'
      simp only [setBackfillPost, capUpd2_apply]
      split_ifs
      · exact hv
      · exact hw.backfill_lt k a'
  | markBackfilled c =>
    obtain ⟨-, rfl⟩ := capStep_markBackfilled.mp h
    refine { hw with interop_not_pending := ?_, pool_not_pending := ?_ }
    · intro c' hc'
      simp only [Function.update_apply]
      split_ifs
      · rfl
      · exact hw.interop_not_pending c' hc'
    · simp only [Function.update_apply]
      split_ifs
      · rfl
      · exact hw.pool_not_pending
  | moveToPool c a =>
    obtain ⟨⟨hi, -, -, -, hcred⟩, rfl⟩ := capStep_moveToPool.mp h
    refine { hw with inPool_interop := ?_, deposited_lt := ?_ }
    · intro c' a' h'
      simp only [movePost, capUpd2_apply] at h'
      split_ifs at h' with hk
      · obtain ⟨rfl, rfl⟩ := hk; exact hi
      · exact hw.inPool_interop c' a' h'
    · intro k a'
      simp only [movePost, capUpd2_apply]
      split_ifs with hk
      · obtain ⟨rfl, rfl⟩ := hk; exact hcred
      · exact hw.deposited_lt k a'
  | initializeUpgrade =>
    obtain ⟨hu, -⟩ := capStep_initializeUpgrade.mp h
    simp [hw.upgraded] at hu
  | enableInterop c =>
    obtain ⟨⟨hr, -, hp⟩, rfl⟩ := capStep_enableInterop.mp h
    refine { hw with interop_registered := ?_, inPool_interop := ?_, interop_not_pending := ?_ }
    · intro c' h'
      simp only [Function.update_apply] at h'
      split_ifs at h' with hc
      · subst hc; exact hr
      · exact hw.interop_registered c' h'
    · intro c' a' h'
      have := hw.inPool_interop c' a' h'
      simp only [Function.update_apply]
      split_ifs <;> simp [this]
    · intro c' h'
      simp only [Function.update_apply] at h'
      split_ifs at h' with hc
      · subst hc; exact hp
      · exact hw.interop_not_pending c' h'
  | registerChain c =>
    obtain ⟨⟨h0, hcap, hl1, -⟩, rfl⟩ := capStep_registerChain.mp h
    refine { hw with registered_valid := ?_, interop_registered := ?_ }
    · intro c' h'
      simp only [Function.update_apply] at h'
      split_ifs at h' with hc
      · subst hc; exact ⟨h0, hcap, hl1⟩
      · exact hw.registered_valid c' h'
    · intro c' h'
      have := hw.interop_registered c' h'
      simp only [Function.update_apply]
      split_ifs <;> simp [this]
  | registerAsset a o =>
    obtain ⟨-, rfl⟩ := capStep_registerAsset.mp h
    exact { hw with }
  | populate a L =>
    obtain ⟨⟨-, -, hb⟩, rfl⟩ := capStep_populate.mp h
    refine { hw with bridgedOut_lt := ?_ }
    intro a'
    simp only [Function.update_apply]
    split_ifs with ha
    · subst ha; exact hb
    · exact hw.bridgedOut_lt a'

theorem capUpgradeState_wf {cfg : CapConfig} {s : CapState} (hok : cfg.Ok)
    (h : CapUpgradeState cfg s) : CapWF cfg s where
  registered_valid := h.registered_valid
  interop_registered := fun c hc => by simp [h.interop_false c] at hc
  inPool_interop := fun c a hc => by simp [h.inPool_false c a] at hc
  interop_not_pending := fun c hc => by simp [h.interop_false c] at hc
  upgraded := h.upgraded
  pool_not_pending := by
    rw [h.pending_eq]
    cases hr : s.registered cfg.pool
    · rfl
    · have := (h.registered_valid _ hr).2.1
      have := hok.2.1
      omega
  pool_backfill_zero := fun a => h.backfill_zero _ a
  deposited_lt := fun k a => by rw [h.deposited_zero]; unfold capWordBound; positivity
  withdrawn_lt := fun k a => by rw [h.withdrawn_zero]; unfold capWordBound; positivity
  backfill_lt := fun k a => by rw [h.backfill_zero]; unfold capWordBound; positivity
  bridgedOut_lt := h.bridgedOut_lt

/-! ## Runs -/

theorem capRun_wf {cfg : CapConfig} {s t : CapState} {ls : List CapLabel}
    (hr : CapRun cfg s ls t) : CapWF cfg s → CapWF cfg t := by
  induction hr with
  | nil => exact id
  | cons h _ ih => exact fun hw => ih (capStep_wf hw h)

theorem BulkheadRunsStayWellFormed : Properties.BulkheadRunsStayWellFormed := by
  intro cfg s0 s ls hok h0 hr
  exact capRun_wf hr (capUpgradeState_wf hok h0)

/-- Monotone fields along a run, and the origin's write-once shape. -/
theorem capRun_mono {cfg : CapConfig} {s t : CapState} {ls : List CapLabel}
    (hr : CapRun cfg s ls t) :
    (∀ c, s.interop c = true → t.interop c = true) ∧
    (∀ c, s.registered c = true → t.registered c = true) ∧
    (s.upgraded = true → t.upgraded = true) ∧
    (∀ k a, s.deposited k a ≤ t.deposited k a) ∧
    (∀ k a, s.backfill k a ≤ t.backfill k a) ∧
    (∀ k a, s.backfill k a ≠ 0 → t.backfill k a = s.backfill k a) ∧
    (∀ k a, s.withdrawn k a ≤ t.withdrawn k a) ∧
    (∀ c a, s.inPool c a = true → t.inPool c a = true) ∧
    (∀ a, t.origin a = s.origin a ∨ s.origin a = 0) := by
  induction hr with
  | nil s => exact ⟨fun _ h => h, fun _ h => h, fun h => h, fun _ _ => le_rfl, fun _ _ => le_rfl,
      fun _ _ _ => rfl, fun _ _ => le_rfl, fun _ _ h => h, fun _ => Or.inl rfl⟩
  | cons h _ ih =>
    obtain ⟨i1, r1, u1, d1, b1, n1, w1, p1, o1⟩ := capStep_mono h
    obtain ⟨i2, r2, u2, d2, b2, n2, w2, p2, o2⟩ := ih
    refine ⟨fun c hc => i2 c (i1 c hc), fun c hc => r2 c (r1 c hc), fun hc => u2 (u1 hc),
      fun k a => (d1 k a).trans (d2 k a), fun k a => (b1 k a).trans (b2 k a), ?_,
      fun k a => (w1 k a).trans (w2 k a), fun c a hc => p2 c a (p1 c a hc), ?_⟩
    · intro k a hne
      have e1 := n1 k a hne
      rw [n2 k a (by rw [e1]; exact hne), e1]
    · intro a
      rcases o1 a with e1 | e1
      · rcases o2 a with e2 | e2
        · exact Or.inl (e2.trans e1)
        · exact Or.inr (e1 ▸ e2)
      · exact Or.inr e1

/-- An intermediate state's origin is the start's or the end's. -/
theorem capRun_origin_mid {cfg : CapConfig} {s u t : CapState} {l : CapLabel}
    {ls : List CapLabel} (h : capStep cfg l s = some u) (hr : CapRun cfg u ls t) (a : ℕ) :
    u.origin a = s.origin a ∨ u.origin a = t.origin a := by
  rcases (capStep_mono h).2.2.2.2.2.2.2.2 a with e | e
  · exact Or.inl e
  · rcases (capRun_mono hr).2.2.2.2.2.2.2.2 a with e' | e'
    · exact Or.inr e'.symm
    · exact Or.inl (e'.trans e.symm)

/-- **Along a run, a key that stays clear has exact accounting and the cap.** -/
theorem capRun_key {cfg : CapConfig} {s t : CapState} {ls : List CapLabel}
    (hr : CapRun cfg s ls t) {k a : ℕ} :
    KeyStaysClear s k →
      t.withdrawn k a = s.withdrawn k a + releasedUnderKey cfg k a s ls ∧
        t.withdrawn k a ≤ max (s.withdrawn k a) (t.deposited k a + t.backfill k a) := by
  induction hr with
  | nil s => intro _; exact ⟨by simp [releasedUnderKey], le_max_left _ _⟩
  | @cons s u t l ls h hr ih =>
    intro hk
    obtain ⟨e2, c2⟩ := ih (capStep_keyStaysClear h hk)
    have e1 := capStep_withdrawn_eq h k a
    have c1 := capStep_withdrawn_le h (k := k) (a := a) hk.1
    obtain ⟨-, -, -, d2, b2, -, -, -, -⟩ := capRun_mono hr
    refine ⟨?_, ?_⟩
    · rw [releasedUnderKey_cons h, e2, e1]; ring
    · have hdb : u.deposited k a + u.backfill k a ≤ t.deposited k a + t.backfill k a :=
        Nat.add_le_add (d2 k a) (b2 k a)
      rcases le_max_iff.mp c2 with h2 | h2
      · rcases le_max_iff.mp c1 with h1 | h1
        · exact le_max_of_le_left (h2.trans h1)
        · exact le_max_of_le_right (h2.trans (h1.trans hdb))
      · exact le_max_of_le_right h2

/-- From the run facts, the three forms of the release bound. -/
theorem capRelease_bounds {w0 w1 d0 d1 b0 b1 r : ℕ} (he : w1 = w0 + r)
    (hc : w1 ≤ max w0 (d1 + b1)) (hd : d0 + b0 ≤ d1 + b1) :
    r = w1 - w0 ∧ w0 ≤ w1 ∧ r ≤ d1 + b1 - w0 ∧ r ≤ (d1 + b1 - (d0 + b0)) + (d0 + b0 - w0) := by
  rcases le_max_iff.mp hc with h | h <;> omega

theorem BulkheadKeyReleaseBound : Properties.BulkheadKeyReleaseBound := by
  intro cfg s t ls k a hr hu hp
  obtain ⟨he, hc⟩ := capRun_key hr (k := k) (a := a) ⟨hp, Or.inl hu⟩
  obtain ⟨-, -, -, d2, b2, -, -, -, -⟩ := capRun_mono hr
  exact capRelease_bounds he hc (Nat.add_le_add (d2 k a) (b2 k a))

/-- For a disabled chain whose own assets are not in play, `_trackedBalance` returns `c` exactly
for `c`'s own calls. -/
theorem capTrackedKey_eq_self_iff {cfg : CapConfig} {s : CapState} {c c' o : ℕ}
    (hi : s.interop c = false) (ho : o ≠ c) (hcp : c ≠ cfg.pool) :
    capTrackedKey cfg s c' o = some c ↔ c' = c := by
  unfold capTrackedKey
  by_cases hc' : c' = c
  · subst hc'; simp [hi, ho]
  · simp only [hc', iff_false]
    split_ifs with h1 h2 h3
    · simp
    · intro e; exact hcp (Option.some.inj e).symm
    · simp
    · intro e; exact hc' (Option.some.inj e)

theorem releasedFrom_eq_underKey {cfg : CapConfig} {s t : CapState} {ls : List CapLabel}
    (hr : CapRun cfg s ls t) {c a : ℕ} (hcp : c ≠ cfg.pool) (hti : t.interop c = false)
    (hto : t.origin a ≠ c) : s.origin a ≠ c → releasedFrom c a ls = releasedUnderKey cfg c a s ls := by
  induction hr with
  | nil s => intro _; simp [releasedFrom, releasedUnderKey]
  | @cons s u t l ls h hr ih =>
    intro hso
    have hsi : s.interop c = false := by
      cases e : s.interop c
      · rfl
      · simp [(capRun_mono hr).1 c ((capStep_mono h).1 c e)] at hti
    have huo : u.origin a ≠ c := by
      rcases capRun_origin_mid h hr a with e | e <;> rw [e] <;> assumption
    rw [releasedUnderKey_cons h, ← ih hti hto huo]
    cases l with
    | fromChain c' a' x =>
      simp only [releasedFrom, capKeyHere]
      by_cases ha : a' = a
      · subst ha
        have := capTrackedKey_eq_self_iff (cfg := cfg) (c' := c') hsi hso hcp
        by_cases hc' : c' = c <;> simp_all
      · simp [ha]
    | _ => simp [releasedFrom, capKeyHere]

theorem BulkheadDisabledChainReleaseBound : Properties.BulkheadDisabledChainReleaseBound := by
  intro cfg s t ls c a hr hu hp hti hcp hso hto
  rw [releasedFrom_eq_underKey hr hcp hti hto hso]
  obtain ⟨he, hc⟩ := capRun_key hr (k := c) (a := a) ⟨hp, Or.inl hu⟩
  obtain ⟨-, -, -, d2, b2, -, -, -, -⟩ := capRun_mono hr
  obtain ⟨h1, -, h3, h4⟩ := capRelease_bounds he hc (Nat.add_le_add (d2 c a) (b2 c a))
  exact ⟨h1, h3, h4⟩

/-- A call's contribution to `releasedByEnabled`. -/
def capEnabledHere (asset : ℕ) (s : CapState) : CapLabel → ℕ
  | .fromChain c a x => if a = asset ∧ s.interop c = true then x else 0
  | _ => 0

theorem releasedByEnabled_cons {cfg : CapConfig} {l : CapLabel} {s t : CapState}
    {ls : List CapLabel} {a : ℕ} (h : capStep cfg l s = some t) :
    releasedByEnabled cfg a s (l :: ls) = capEnabledHere a s l + releasedByEnabled cfg a t ls := by
  cases l <;> simp [releasedByEnabled, capEnabledHere, h]

theorem releasedByEnabled_eq_underKey {cfg : CapConfig} {s t : CapState} {ls : List CapLabel}
    (hok : cfg.Ok) (hr : CapRun cfg s ls t) {a : ℕ} (hti : t.interop (t.origin a) = false) :
    CapWF cfg s → releasedByEnabled cfg a s ls = releasedUnderKey cfg cfg.pool a s ls := by
  induction hr with
  | nil s => intro _; simp [releasedByEnabled, releasedUnderKey]
  | @cons s u t l ls h hr ih =>
    intro hw
    rw [releasedByEnabled_cons h, releasedUnderKey_cons h, ih hti (capStep_wf hw h)]
    congr 1
    have hsi : s.interop (s.origin a) = false := by
      rcases (capRun_mono (CapRun.cons h hr)).2.2.2.2.2.2.2.2 a with e | e
      · rw [← e]
        cases e' : s.interop (t.origin a)
        · rfl
        · simp [(capRun_mono (CapRun.cons h hr)).1 _ e'] at hti
      · rw [e]; exact hw.zero_not_interop
    cases l with
    | fromChain c' a' x =>
      obtain ⟨⟨hreg, -⟩, -⟩ := capStep_fromChain.mp h
      have hne := hw.ne_pool hok hreg
      simp only [capEnabledHere, capKeyHere]
      by_cases ha : a' = a
      · subst ha
        unfold capTrackedKey
        by_cases hc : s.interop c' = true
        · simp [hc, hsi]
        · have hc' : s.interop c' = false := by simpa using hc
          by_cases ho : s.origin a' = c' <;> simp [hc', ho, hne]
      · simp [ha]
    | _ => simp [capEnabledHere, capKeyHere]

theorem BulkheadEnabledSetReleaseBound : Properties.BulkheadEnabledSetReleaseBound := by
  intro cfg s t ls a hok hw hr hti
  rw [releasedByEnabled_eq_underKey hok hr hti hw]
  obtain ⟨he, hc⟩ := capRun_key hr (k := cfg.pool) (a := a) ⟨hw.pool_not_pending, Or.inl hw.upgraded⟩
  obtain ⟨-, -, -, d2, -, -, -, -, -⟩ := capRun_mono hr
  have hwt := capRun_wf hr hw
  rw [hwt.pool_backfill_zero, Nat.add_zero] at hc
  have hd := d2 cfg.pool a
  rcases le_max_iff.mp hc with h | h <;> refine ⟨?_, ?_, ?_⟩ <;> omega

/-! ## (a) and (c) -/

theorem BulkheadCappedWithdrawalWithinLimit : Properties.BulkheadCappedWithdrawalWithinLimit := by
  intro cfg s t c a x k h hk hp
  obtain ⟨⟨-, -, -, hw⟩, rfl⟩ := capStep_fromChain.mp h
  have hle := ((hw k hk).2 hp).2
  have e : (fromChainPost cfg s c a x).withdrawn k a = s.withdrawn k a + x := by
    simp [fromChainPost, hk]
  exact ⟨e, rfl, rfl, by rw [e]; exact hle⟩

theorem BulkheadCrossChainFrame : Properties.BulkheadCrossChainFrame := by
  intro cfg s t l d h hdp hdc
  exact capStep_frame h hdp hdc

/-! ## (d) The ledger identity -/

/-- A chain's term in the potential: `withdrawn - deposited` until its balance moves to the pool,
`max backfill (withdrawn - deposited)` after. -/
def capPhi (s : CapState) (a c : ℕ) : ℤ :=
  if s.inPool c a = true then max (s.backfill c a : ℤ) ((s.withdrawn c a : ℤ) - s.deposited c a)
  else (s.withdrawn c a : ℤ) - s.deposited c a

/-- The quantity every call changes by exactly the legacy amount it populates. -/
def capPotential (cfg : CapConfig) (s : CapState) (a : ℕ) : ℤ :=
  (s.bridgedOut a : ℤ) + ∑ c ∈ range chainIdCap, capPhi s a c
    - ((s.deposited cfg.pool a : ℤ) - s.withdrawn cfg.pool a)

/-- A call's contribution to `populatedIn`. -/
def capPopHere (a : ℕ) : CapLabel → ℕ
  | .populate a' L => if a' = a then L else 0
  | _ => 0

theorem populatedIn_cons (a : ℕ) (l : CapLabel) (ls : List CapLabel) :
    populatedIn a (l :: ls) = capPopHere a l + populatedIn a ls := by
  cases l <;> simp [populatedIn, capPopHere]

theorem capSum_update {T : Finset ℕ} {f g : ℕ → ℤ} (c0 : ℕ) (h : ∀ c ∈ T, c ≠ c0 → g c = f c) :
    ∑ c ∈ T, g c = ∑ c ∈ T, f c + (if c0 ∈ T then g c0 - f c0 else 0) := by
  have : ∑ c ∈ T, g c - ∑ c ∈ T, f c = ∑ c ∈ T, (if c = c0 then g c0 - f c0 else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c hcT
    by_cases hc : c = c0
    · subst hc; simp
    · simp [hc, h c hcT hc]
  rw [Finset.sum_ite_eq'] at this
  linarith

theorem capPhi_credit (d v w : ℕ) :
    max (v : ℤ) ((w : ℤ) - d) - max ((0 : ℕ) : ℤ) ((w : ℤ) - d) = (((d + v - w) - (d - w) : ℕ) : ℤ) := by
  simp only [max_def]
  split_ifs <;> omega

theorem capPhi_move (d b w : ℕ) :
    max (b : ℤ) ((w : ℤ) - d) - ((w : ℤ) - d) = ((d + b - w : ℕ) : ℤ) := by
  simp only [max_def]
  split_ifs <;> omega

/-- **The potential, one call.** -/
theorem capStep_potential {cfg : CapConfig} {l : CapLabel} {s t : CapState} {a : ℕ}
    (hok : cfg.Ok) (hw : CapWF cfg s) (ho : s.origin a = cfg.l1) (h : capStep cfg l s = some t) :
    capPotential cfg t a = capPotential cfg s a + capPopHere a l := by
  have hpool : cfg.pool ∉ range chainIdCap := by simp [hok.2.1]
  cases l with
  | toChain c a' x =>
    obtain ⟨⟨hreg, -, -, -⟩, rfl⟩ := capStep_toChain.mp h
    simp only [capPopHere, Nat.cast_zero, add_zero]
    by_cases ha : a' = a
    · subst ha
      obtain ⟨-, hccap, hcl1⟩ := hw.registered_valid c hreg
      have hcmem : c ∈ range chainIdCap := by simp [hccap]
      have hcp : c ≠ cfg.pool := hw.ne_pool hok hreg
      have hbo : (toChainPost cfg s c a' x).bridgedOut a' = s.bridgedOut a' + x := by
        simp [toChainPost, ho]
      by_cases hi : s.interop c = true
      · have hk : capTrackedKey cfg s c (s.origin a') = some cfg.pool := by
          simp [capTrackedKey, hi, ho, hw.l1_not_interop]
        have hdep : ∀ k, (toChainPost cfg s c a' x).deposited k a' =
            s.deposited k a' + (if k = cfg.pool then x else 0) := by
          intro k; simp only [toChainPost, capBump_apply, hk, Option.some.injEq]
          by_cases hkp : k = cfg.pool
          · subst hkp; simp
          · simp [hkp, Ne.symm hkp]
        have hsum : ∑ c' ∈ range chainIdCap, capPhi (toChainPost cfg s c a' x) a' c' =
            ∑ c' ∈ range chainIdCap, capPhi s a' c' := by
          apply Finset.sum_congr rfl
          intro c' hc'
          have : c' ≠ cfg.pool := fun e => hpool (e ▸ hc')
          simp only [capPhi, hdep, this, ite_false, add_zero]
          rfl
        unfold capPotential
        rw [hsum, hbo, hdep]
        simp only [ite_true]
        have : (toChainPost cfg s c a' x).withdrawn = s.withdrawn := rfl
        rw [this]; push_cast; ring
      · have hi' : s.interop c = false := by simpa using hi
        have hk : capTrackedKey cfg s c (s.origin a') = some c := by
          simp [capTrackedKey, hi', ho, Ne.symm hcl1]
        have hdep : ∀ k, (toChainPost cfg s c a' x).deposited k a' =
            s.deposited k a' + (if k = c then x else 0) := by
          intro k; simp only [toChainPost, capBump_apply, hk, Option.some.injEq]
          by_cases hkc : k = c
          · subst hkc; simp
          · simp [hkc, Ne.symm hkc]
        have hnp := hw.not_inPool (a := a') hi'
        have hsum : ∑ c' ∈ range chainIdCap, capPhi (toChainPost cfg s c a' x) a' c' =
            ∑ c' ∈ range chainIdCap, capPhi s a' c' - x := by
          rw [capSum_update (f := capPhi s a') c (fun c' hT hc' => by
            have : c' ≠ cfg.pool := fun e => hpool (e ▸ hT)
            simp only [capPhi, hdep, hc', ite_false, add_zero]; rfl)]
          simp only [hcmem, ite_true, capPhi, hdep, ite_true]
          have : (toChainPost cfg s c a' x).inPool = s.inPool := rfl
          rw [this, hnp]
          have : (toChainPost cfg s c a' x).withdrawn = s.withdrawn := rfl
          rw [this]
          simp only [Bool.false_eq_true, ite_false]
          push_cast; ring
        unfold capPotential
        rw [hsum, hbo, hdep]
        simp only [Ne.symm hcp, ite_false, add_zero]
        have : (toChainPost cfg s c a' x).withdrawn = s.withdrawn := rfl
        rw [this]; push_cast; ring
    · have hbo : (toChainPost cfg s c a' x).bridgedOut a = s.bridgedOut a := by
        simp only [toChainPost]; split_ifs <;> simp [Ne.symm ha]
      have hdep : ∀ k, (toChainPost cfg s c a' x).deposited k a = s.deposited k a := by
        intro k; simp [toChainPost, capBump_apply, Ne.symm ha]
      have hsum : ∑ c' ∈ range chainIdCap, capPhi (toChainPost cfg s c a' x) a c' =
          ∑ c' ∈ range chainIdCap, capPhi s a c' :=
        Finset.sum_congr rfl (fun c' _ => by simp only [capPhi, hdep]; rfl)
      unfold capPotential
      rw [hbo, hdep, hsum]
      rfl
  | fromChain c a' x =>
    obtain ⟨⟨hreg, -, hbo', hallow⟩, rfl⟩ := capStep_fromChain.mp h
    simp only [capPopHere, Nat.cast_zero, add_zero]
    by_cases ha : a' = a
    · subst ha
      obtain ⟨-, hccap, hcl1⟩ := hw.registered_valid c hreg
      have hcmem : c ∈ range chainIdCap := by simp [hccap]
      have hcp : c ≠ cfg.pool := hw.ne_pool hok hreg
      have hxle := hbo' ho
      have hbo : ((fromChainPost cfg s c a' x).bridgedOut a' : ℤ) = s.bridgedOut a' - x := by
        simp [fromChainPost, ho, Nat.cast_sub hxle]
      by_cases hi : s.interop c = true
      · have hk : capTrackedKey cfg s c (s.origin a') = some cfg.pool := by
          simp [capTrackedKey, hi, ho, hw.l1_not_interop]
        have hwd : ∀ k, (fromChainPost cfg s c a' x).withdrawn k a' =
            s.withdrawn k a' + (if k = cfg.pool then x else 0) := by
          intro k; simp only [fromChainPost, capBump_apply, hk, Option.some.injEq]
          by_cases hkp : k = cfg.pool
          · subst hkp; simp
          · simp [hkp, Ne.symm hkp]
        have hsum : ∑ c' ∈ range chainIdCap, capPhi (fromChainPost cfg s c a' x) a' c' =
            ∑ c' ∈ range chainIdCap, capPhi s a' c' := by
          apply Finset.sum_congr rfl
          intro c' hc'
          have : c' ≠ cfg.pool := fun e => hpool (e ▸ hc')
          simp only [capPhi, hwd, this, ite_false, add_zero]
          rfl
        unfold capPotential
        rw [hsum, hbo, hwd]
        simp only [ite_true]
        have : (fromChainPost cfg s c a' x).deposited = s.deposited := rfl
        rw [this]; push_cast; ring
      · have hi' : s.interop c = false := by simpa using hi
        have hk : capTrackedKey cfg s c (s.origin a') = some c := by
          simp [capTrackedKey, hi', ho, Ne.symm hcl1]
        have hwd : ∀ k, (fromChainPost cfg s c a' x).withdrawn k a' =
            s.withdrawn k a' + (if k = c then x else 0) := by
          intro k; simp only [fromChainPost, capBump_apply, hk, Option.some.injEq]
          by_cases hkc : k = c
          · subst hkc; simp
          · simp [hkc, Ne.symm hkc]
        have hnp := hw.not_inPool (a := a') hi'
        have hsum : ∑ c' ∈ range chainIdCap, capPhi (fromChainPost cfg s c a' x) a' c' =
            ∑ c' ∈ range chainIdCap, capPhi s a' c' + x := by
          rw [capSum_update (f := capPhi s a') c (fun c' hT hc' => by
            have : c' ≠ cfg.pool := fun e => hpool (e ▸ hT)
            simp only [capPhi, hwd, hc', ite_false, add_zero]; rfl)]
          simp only [hcmem, ite_true, capPhi, hwd, ite_true]
          have : (fromChainPost cfg s c a' x).inPool = s.inPool := rfl
          rw [this, hnp]
          have : (fromChainPost cfg s c a' x).deposited = s.deposited := rfl
          rw [this]
          simp only [Bool.false_eq_true, ite_false]
          push_cast; ring
        unfold capPotential
        rw [hsum, hbo, hwd]
        simp only [Ne.symm hcp, ite_false, add_zero]
        have : (fromChainPost cfg s c a' x).deposited = s.deposited := rfl
        rw [this]; ring
    · have hbo : (fromChainPost cfg s c a' x).bridgedOut a = s.bridgedOut a := by
        simp only [fromChainPost]; split_ifs <;> simp [Ne.symm ha]
      have hwd : ∀ k, (fromChainPost cfg s c a' x).withdrawn k a = s.withdrawn k a := by
        intro k; simp [fromChainPost, capBump_apply, Ne.symm ha]
      have hsum : ∑ c' ∈ range chainIdCap, capPhi (fromChainPost cfg s c a' x) a c' =
          ∑ c' ∈ range chainIdCap, capPhi s a c' :=
        Finset.sum_congr rfl (fun c' _ => by simp only [capPhi, hwd]; rfl)
      unfold capPotential
      rw [hbo, hwd, hsum]
      rfl
  | setBackfill c a' v =>
    obtain ⟨⟨hcp, -, hz, -⟩, rfl⟩ := capStep_setBackfill.mp h
    simp only [capPopHere, Nat.cast_zero, add_zero]
    have hwd : (setBackfillPost cfg s c a' v).withdrawn = s.withdrawn := rfl
    have hin : (setBackfillPost cfg s c a' v).inPool = s.inPool := rfl
    have hbo : (setBackfillPost cfg s c a' v).bridgedOut = s.bridgedOut := rfl
    by_cases ha : a' = a
    · subst ha
      have hbf : ∀ k, (setBackfillPost cfg s c a' v).backfill k a' =
          if k = c then v else s.backfill k a' := by
        intro k; simp [setBackfillPost, capUpd2_apply]
      by_cases hp : s.inPool c a' = true
      · have hcreg := hw.interop_registered c (hw.inPool_interop c a' hp)
        have hcmem : c ∈ range chainIdCap := by
          simp [(hw.registered_valid c hcreg).2.1]
        have hdep : ∀ k, (setBackfillPost cfg s c a' v).deposited k a' =
            s.deposited k a' + (if k = cfg.pool then setBackfillCredit s c a' v else 0) := by
          intro k
          simp only [setBackfillPost, hp, ite_true, capUpd2_apply]
          by_cases hkp : k = cfg.pool
          · subst hkp; simp
          · simp [hkp]
        have hsum : ∑ c' ∈ range chainIdCap, capPhi (setBackfillPost cfg s c a' v) a' c' =
            ∑ c' ∈ range chainIdCap, capPhi s a' c' + setBackfillCredit s c a' v := by
          rw [capSum_update (f := capPhi s a') c (fun c' hT hc' => by
            have : c' ≠ cfg.pool := fun e => hpool (e ▸ hT)
            simp only [capPhi, hdep, hbf, hc', this, hwd, hin, ite_false, add_zero])]
          simp only [hcmem, ite_true, capPhi, hdep, hbf, hwd, hin, hp, hcp, ite_false,
            add_zero, hz]
          rw [capPhi_credit]
          rfl
        unfold capPotential
        rw [hsum, hdep, hbo, hwd]
        simp only [ite_true]
        push_cast; ring
      · have hp' : s.inPool c a' = false := by simpa using hp
        have hdep : (setBackfillPost cfg s c a' v).deposited = s.deposited := by
          simp [setBackfillPost, hp']
        have hsum : ∑ c' ∈ range chainIdCap, capPhi (setBackfillPost cfg s c a' v) a' c' =
            ∑ c' ∈ range chainIdCap, capPhi s a' c' := by
          apply Finset.sum_congr rfl
          intro c' _
          simp only [capPhi, hin, hwd, hdep, hbf]
          by_cases hc' : c' = c
          · subst hc'; simp [hp']
          · simp [hc']
        unfold capPotential
        rw [hdep, hbo, hwd, hsum]
    · have hdep : ∀ k, (setBackfillPost cfg s c a' v).deposited k a = s.deposited k a := by
        intro k; simp only [setBackfillPost]; split_ifs <;> simp [capUpd2_apply, Ne.symm ha]
      have hbf : ∀ k, (setBackfillPost cfg s c a' v).backfill k a = s.backfill k a := by
        intro k; simp [setBackfillPost, capUpd2_apply, Ne.symm ha]
      have hsum : ∑ c' ∈ range chainIdCap, capPhi (setBackfillPost cfg s c a' v) a c' =
          ∑ c' ∈ range chainIdCap, capPhi s a c' :=
        Finset.sum_congr rfl (fun c' _ => by simp only [capPhi, hin, hwd, hdep, hbf])
      unfold capPotential
      rw [hdep, hbo, hwd, hsum]
  | markBackfilled c =>
    obtain ⟨-, rfl⟩ := capStep_markBackfilled.mp h
    simp [capPopHere, capPotential, capPhi]
  | moveToPool c a' =>
    obtain ⟨⟨hi, -, hnp, -, -⟩, rfl⟩ := capStep_moveToPool.mp h
    simp only [capPopHere, Nat.cast_zero, add_zero]
    have hwd : (movePost cfg s c a').withdrawn = s.withdrawn := rfl
    have hbf : (movePost cfg s c a').backfill = s.backfill := rfl
    have hbo : (movePost cfg s c a').bridgedOut = s.bridgedOut := rfl
    by_cases ha : a' = a
    · subst ha
      have hcreg := hw.interop_registered c hi
      have hcmem : c ∈ range chainIdCap := by simp [(hw.registered_valid c hcreg).2.1]
      have hcp : c ≠ cfg.pool := hw.ne_pool hok hcreg
      have hdep : ∀ k, (movePost cfg s c a').deposited k a' =
          s.deposited k a' + (if k = cfg.pool then moveCredit s c a' else 0) := by
        intro k
        simp only [movePost, capUpd2_apply]
        by_cases hkp : k = cfg.pool
        · subst hkp; simp
        · simp [hkp]
      have hin : ∀ k, (movePost cfg s c a').inPool k a' = if k = c then true else s.inPool k a' := by
        intro k; simp [movePost, capUpd2_apply]
      have hsum : ∑ c' ∈ range chainIdCap, capPhi (movePost cfg s c a') a' c' =
          ∑ c' ∈ range chainIdCap, capPhi s a' c' + moveCredit s c a' := by
        rw [capSum_update (f := capPhi s a') c (fun c' hT hc' => by
          have : c' ≠ cfg.pool := fun e => hpool (e ▸ hT)
          simp only [capPhi, hdep, hin, hc', this, hwd, hbf, ite_false, add_zero])]
        simp only [hcmem, ite_true, capPhi, hdep, hin, hwd, hbf, hnp, hcp, ite_false, add_zero,
          Bool.false_eq_true]
        rw [capPhi_move]
        rfl
      unfold capPotential
      rw [hsum, hdep, hbo, hwd]
      simp only [ite_true]
      push_cast; ring
    · have hdep : ∀ k, (movePost cfg s c a').deposited k a = s.deposited k a := by
        intro k; simp [movePost, capUpd2_apply, Ne.symm ha]
      have hin : ∀ k, (movePost cfg s c a').inPool k a = s.inPool k a := by
        intro k; simp [movePost, capUpd2_apply, Ne.symm ha]
      have hsum : ∑ c' ∈ range chainIdCap, capPhi (movePost cfg s c a') a c' =
          ∑ c' ∈ range chainIdCap, capPhi s a c' :=
        Finset.sum_congr rfl (fun c' _ => by simp only [capPhi, hin, hwd, hdep, hbf])
      unfold capPotential
      rw [hdep, hbo, hwd, hsum]
  | initializeUpgrade =>
    obtain ⟨-, rfl⟩ := capStep_initializeUpgrade.mp h
    simp [capPopHere, capPotential, capPhi]
  | enableInterop c =>
    obtain ⟨-, rfl⟩ := capStep_enableInterop.mp h
    simp [capPopHere, capPotential, capPhi]
  | registerChain c =>
    obtain ⟨-, rfl⟩ := capStep_registerChain.mp h
    simp [capPopHere, capPotential, capPhi]
  | registerAsset a' o =>
    obtain ⟨-, rfl⟩ := capStep_registerAsset.mp h
    simp [capPopHere, capPotential, capPhi]
  | populate a' L =>
    obtain ⟨-, ht⟩ := capStep_populate.mp h
    have hsum : ∑ c' ∈ range chainIdCap, capPhi t a c' = ∑ c' ∈ range chainIdCap, capPhi s a c' := by
      rw [ht]; rfl
    have hdep : t.deposited = s.deposited := by rw [ht]
    have hwd : t.withdrawn = s.withdrawn := by rw [ht]
    have hbo : t.bridgedOut = Function.update s.bridgedOut a' (s.bridgedOut a' + L) := by rw [ht]
    unfold capPotential capPopHere
    rw [hsum, hdep, hwd, hbo]
    by_cases ha : a' = a
    · subst ha
      simp only [Function.update_apply, ite_true]
      push_cast; ring
    · simp only [Function.update_apply, Ne.symm ha, ha, ite_false, Nat.cast_zero, add_zero]

/-- An L1-native asset stays L1-native along a run (`L1_CHAIN_ID ≠ 0`). -/
theorem capRun_origin_l1 {cfg : CapConfig} {s t : CapState} {ls : List CapLabel} {a : ℕ}
    (hok : cfg.Ok) (hr : CapRun cfg s ls t) (ho : s.origin a = cfg.l1) : t.origin a = cfg.l1 := by
  rcases (capRun_mono hr).2.2.2.2.2.2.2.2 a with e | e
  · rw [e, ho]
  · rw [ho] at e; exact absurd e (Nat.pos_iff_ne_zero.mp hok.1)

/-- **The potential along a run.** -/
theorem capRun_potential {cfg : CapConfig} {s t : CapState} {ls : List CapLabel} {a : ℕ}
    (hok : cfg.Ok) (hr : CapRun cfg s ls t) :
    CapWF cfg s → s.origin a = cfg.l1 →
      capPotential cfg t a = capPotential cfg s a + populatedIn a ls := by
  induction hr with
  | nil s => intro _ _; simp [populatedIn]
  | @cons s u t l ls h hr ih =>
    intro hw ho
    have hou : u.origin a = cfg.l1 := capRun_origin_l1 hok (CapRun.cons h (CapRun.nil u)) ho
    rw [ih (capStep_wf hw h) hou, capStep_potential hok hw ho h, populatedIn_cons]
    push_cast; ring

theorem capPotential_upgrade {cfg : CapConfig} {s : CapState} (h : CapUpgradeState cfg s)
    (a : ℕ) : capPotential cfg s a = s.bridgedOut a := by
  unfold capPotential capPhi
  simp [h.inPool_false, h.withdrawn_zero, h.deposited_zero]

theorem capPhi_split (s : CapState) (a c : ℕ) :
    capPhi s a c = (s.backfill c a : ℤ) + (if s.inPool c a = true then (capDeficit s c a : ℤ) else 0)
      - (if s.inPool c a = true then 0 else capHeadroom s c a) := by
  unfold capPhi capDeficit capHeadroom
  split_ifs
  · simp only [max_def]; split_ifs <;> omega
  · ring

theorem BulkheadLedgerIdentity : Properties.BulkheadLedgerIdentity := by
  intro cfg s0 s ls a hok h0 hr ho
  have hw0 := capUpgradeState_wf hok h0
  have hws := capRun_wf hr hw0
  have hp := capRun_potential hok hr hw0 ho
  rw [capPotential_upgrade h0] at hp
  unfold capPotential at hp
  have hsplit : ∑ c ∈ range chainIdCap, capPhi s a c =
      ∑ c ∈ range chainIdCap, (s.backfill c a : ℤ)
        + ∑ c ∈ range chainIdCap, (if s.inPool c a = true then (capDeficit s c a : ℤ) else 0)
        - ∑ c ∈ range chainIdCap, (if s.inPool c a = true then 0 else capHeadroom s c a) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun c _ => capPhi_split s a c)
  have hpool : capHeadroom s cfg.pool a = (s.deposited cfg.pool a : ℤ) - s.withdrawn cfg.pool a := by
    unfold capHeadroom; rw [hws.pool_backfill_zero]; simp
  rw [hsplit] at hp
  rw [hpool]
  linarith

theorem BulkheadEscrowBacksHeadroom : Properties.BulkheadEscrowBacksHeadroom := by
  intro cfg s0 s ls a hok h0 hr ho hbudget hmoved
  have hid := BulkheadLedgerIdentity cfg s0 s ls a hok h0 hr ho
  have hdef : ∑ c ∈ range chainIdCap,
      (if s.inPool c a = true then (capDeficit s c a : ℤ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro c _
    split_ifs with hp
    · have h1 := hmoved c hp
      unfold capHeadroom at h1
      unfold capDeficit
      have : s.withdrawn c a ≤ s.deposited c a + s.backfill c a := by omega
      simp [Nat.sub_eq_zero_of_le this]
    · rfl
  have hb : ((∑ c ∈ range chainIdCap, s.backfill c a : ℕ) : ℤ) ≤
      ((s0.bridgedOut a + populatedIn a ls : ℕ) : ℤ) := by exact_mod_cast hbudget
  push_cast at hb
  linarith

theorem BulkheadHonestWithdrawalSucceeds : Properties.BulkheadHonestWithdrawalSucceeds := by
  intro cfg s0 s ls a c x hok h0 hr ho hbudget hnodef hreg hint hpend hlt hx
  have hws := capRun_wf hr (capUpgradeState_wf hok h0)
  have hos : s.origin a = cfg.l1 := capRun_origin_l1 hok hr ho
  have hback := BulkheadEscrowBacksHeadroom cfg s0 s ls a hok h0 hr ho hbudget (fun c _ => hnodef c)
  have hcmem : c ∈ range chainIdCap := by simp [(hws.registered_valid c hreg).2.1]
  have hnp : s.inPool c a = false := hws.not_inPool hint
  have hle : capHeadroom s c a ≤
      ∑ k ∈ range chainIdCap, (if s.inPool k a = true then 0 else capHeadroom s k a) := by
    have := Finset.single_le_sum
      (f := fun k => if s.inPool k a = true then 0 else capHeadroom s k a)
      (fun k _ => by split_ifs; exacts [le_rfl, hnodef k]) hcmem
    simpa [hnp] using this
  have hpool := hnodef cfg.pool
  have hxbo : (x : ℤ) ≤ s.bridgedOut a := by linarith
  have hcl1 : c ≠ cfg.l1 := (hws.registered_valid c hreg).2.2
  have hk : capTrackedKey cfg s c (s.origin a) = some c := by
    simp [capTrackedKey, hint, hos, Ne.symm hcl1]
  unfold capHeadroom at hx
  refine ⟨_, capStep_fromChain.mpr ⟨⟨hreg, by omega, fun _ => by exact_mod_cast hxbo,
    fun k hk' => ?_⟩, rfl⟩⟩
  rw [hk] at hk'
  cases hk'
  exact ⟨by omega, fun _ => ⟨hlt, by omega⟩⟩

theorem BulkheadBridgedWithdrawalSucceeds : Properties.BulkheadBridgedWithdrawalSucceeds := by
  intro cfg s a c x hol1 hoc hreg hint hpend hlt hx
  have hk : capTrackedKey cfg s c (s.origin a) = some c := by simp [capTrackedKey, hint, hoc]
  unfold capHeadroom at hx
  refine ⟨_, capStep_fromChain.mpr ⟨⟨hreg, by omega, fun h => absurd h hol1, fun k hk' => ?_⟩, rfl⟩⟩
  rw [hk] at hk'
  cases hk'
  exact ⟨by omega, fun _ => ⟨hlt, by omega⟩⟩

/-- No call sets a pending flag once the upgrade has run. -/
theorem capStep_pending_false {cfg : CapConfig} {l : CapLabel} {s t : CapState}
    (hw : CapWF cfg s) (h : capStep cfg l s = some t) {c : ℕ} (hc : s.pending c = false) :
    t.pending c = false :=
  (capStep_keyStaysClear h ⟨hc, Or.inl hw.upgraded⟩).1

theorem capStep_noDeficit {cfg : CapConfig} {l : CapLabel} {s t : CapState} {a : ℕ}
    (hw : CapWF cfg s) (h : capStep cfg l s = some t)
    (hp : ∀ c, s.pending c = false) (hd : ∀ k, 0 ≤ capHeadroom s k a) :
    (∀ c, t.pending c = false) ∧ ∀ k, 0 ≤ capHeadroom t k a := by
  refine ⟨fun c => capStep_pending_false hw h (hp c), fun k => ?_⟩
  have hcap := capStep_withdrawn_le h (k := k) (a := a) (hp k)
  obtain ⟨-, -, -, hdm, hbm, -, -, -, -⟩ := capStep_mono h
  have h0 := hd k
  have h1 := hdm k a
  have h2 := hbm k a
  unfold capHeadroom at *
  rcases le_max_iff.mp hcap with h3 | h3 <;> omega

theorem BulkheadNoDeficitPersists : Properties.BulkheadNoDeficitPersists := by
  intro cfg s t ls a _ hw hr hp hd
  induction hr with
  | nil s => exact ⟨hp, hd⟩
  | @cons s u t l ls h hr ih =>
    obtain ⟨hp', hd'⟩ := capStep_noDeficit hw h hp hd
    exact ih (capStep_wf hw h) hp' hd'

/-! ## Concrete runs on the deployed constants -/

theorem deployedCapConfig_ok : deployedCapConfig.Ok := ⟨by decide, by decide, by decide⟩

/-- Execute a list of calls, `none` at the first revert. -/
def capExec (cfg : CapConfig) : CapState → List CapLabel → Option CapState
  | s, [] => some s
  | s, l :: ls =>
    match capStep cfg l s with
    | none => none
    | some t => capExec cfg t ls

theorem capRun_of_exec {cfg : CapConfig} {ls : List CapLabel} :
    ∀ {s t : CapState}, capExec cfg s ls = some t → CapRun cfg s ls t := by
  induction ls with
  | nil => intro s t h; simp only [capExec, Option.some.injEq] at h; subst h; exact CapRun.nil _
  | cons l ls ih =>
    intro s t h
    simp only [capExec] at h
    split at h
    · cases h
    · rename_i u hu; exact CapRun.cons hu (ih h)

theorem capOption_getD {α : Type} {o : Option α} {d : α} (h : o.isSome = true) :
    o = some (o.getD d) := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
  rw [hx]; rfl

theorem capRun_snoc {cfg : CapConfig} {s u t : CapState} {ls : List CapLabel} {l : CapLabel}
    (hr : CapRun cfg s ls u) (h : capStep cfg l u = some t) : CapRun cfg s (ls ++ [l]) t := by
  induction hr with
  | nil s => exact CapRun.cons h (CapRun.nil t)
  | cons h' _ ih => exact CapRun.cons h' (ih h)

theorem capRun_keyStaysClear {cfg : CapConfig} {s t : CapState} {ls : List CapLabel}
    (hr : CapRun cfg s ls t) {k : ℕ} : KeyStaysClear s k → KeyStaysClear t k := by
  induction hr with
  | nil s => exact id
  | cons h _ ih => exact fun hk => ih (capStep_keyStaysClear h hk)

/-- Along a run whose calls name neither `d` nor `initializeUpgrade`, `d`'s counters and flags
stay (`d` not the pool key). -/
theorem capRun_frame {cfg : CapConfig} {s t : CapState} {ls : List CapLabel}
    (hr : CapRun cfg s ls t) {d : ℕ} (hdp : d ≠ cfg.pool)
    (hls : ∀ l ∈ ls, l.chain? ≠ some d ∧ l ≠ .initializeUpgrade) :
    t.deposited d = s.deposited d ∧ t.withdrawn d = s.withdrawn d ∧
      t.backfill d = s.backfill d ∧ t.inPool d = s.inPool d ∧ t.pending d = s.pending d := by
  induction hr with
  | nil s => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | @cons s u t l ls h hr ih =>
    have hl := hls l List.mem_cons_self
    obtain ⟨e1, e2, e3, e4, -, -, e7⟩ := capStep_frame h hdp hl.1
    obtain ⟨f1, f2, f3, f4, f5⟩ := ih (fun l' hl' => hls l' (List.mem_cons_of_mem _ hl'))
    exact ⟨f1.trans e1, f2.trans e2, f3.trans e3, f4.trans e4, f5.trans (e7 hl.2)⟩

theorem capSum_pair {M : Type} [AddCommMonoid M] {T : Finset ℕ} {f : ℕ → M} {p q : ℕ}
    (hp : p ∈ T) (hq : q ∈ T) (hpq : p ≠ q) (h : ∀ k ∈ T, k ≠ p → k ≠ q → f k = 0) :
    ∑ k ∈ T, f k = f p + f q := by
  rw [← Finset.sum_subset (s₁ := {p, q}) (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption)
    (fun x hx hx' => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx'
      exact h x hx hx'.1 hx'.2)]
  exact Finset.sum_pair hpq

theorem capRange_ne_pool {k : ℕ} (hk : k ∈ range chainIdCap) : k ≠ deployedCapConfig.pool := by
  intro e
  rw [e] at hk
  exact absurd (Finset.mem_range.mp hk) (by decide)

/-- The start state of the concrete runs: chains 2 and 3 registered before the upgrade (so
pending), asset 10 native to L1 with `bridgedOut = b0` (populated or not), assets 11 and 12 native
to chains 2 and 3. -/
def capDemoStart (b0 : ℕ) (pop : Bool) : CapState where
  bridgedOut := fun a => if a = 10 then b0 else 0
  populated := fun a => if a = 10 then pop else true
  deposited := fun _ _ => 0
  withdrawn := fun _ _ => 0
  backfill := fun _ _ => 0
  inPool := fun _ _ => false
  pending := fun c => decide (c = 2 ∨ c = 3)
  upgraded := true
  interop := fun _ => false
  registered := fun c => decide (c = 2 ∨ c = 3)
  origin := fun a => if a = 10 then 1 else if a = 11 then 2 else if a = 12 then 3 else 0

theorem capDemoStart_upgrade {b0 : ℕ} (pop : Bool) (hb : b0 < capWordBound) :
    CapUpgradeState deployedCapConfig (capDemoStart b0 pop) where
  deposited_zero := fun _ _ => rfl
  withdrawn_zero := fun _ _ => rfl
  backfill_zero := fun _ _ => rfl
  inPool_false := fun _ _ => rfl
  interop_false := fun _ => rfl
  upgraded := rfl
  pending_eq := fun _ => rfl
  registered_valid := by
    intro c hc
    simp only [capDemoStart, decide_eq_true_eq] at hc
    rcases hc with rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩
  bridgedOut_lt := by
    intro a
    simp only [capDemoStart]
    split_ifs
    · exact hb
    · unfold capWordBound; positivity

/-! ### Countermodel (1) -/

/-- Chain 3 gets its backfill of 60 in the L1-native asset 10 and is marked; chain 2 stays
pending.  Then (`capCmPendingT`) chain 2 withdraws all 100 of `bridgedOut`. -/
def capCmPendingLs : List CapLabel := [.setBackfill 3 10 60, .markBackfilled 3]

def capCmPendingS : CapState :=
  (capExec deployedCapConfig (capDemoStart 100 true) capCmPendingLs).getD (capDemoStart 100 true)

def capCmPendingT : CapState :=
  (capStep deployedCapConfig (.fromChain 2 10 100) capCmPendingS).getD capCmPendingS

theorem BulkheadPendingChainUncapped : Properties.BulkheadPendingChainUncapped := by
  have hrun : CapRun deployedCapConfig (capDemoStart 100 true) capCmPendingLs capCmPendingS :=
    capRun_of_exec (capOption_getD (by decide))
  have hstep : capStep deployedCapConfig (.fromChain 2 10 100) capCmPendingS = some capCmPendingT :=
    capOption_getD (by decide)
  have hsum : ∑ k ∈ range chainIdCap, capCmPendingS.backfill k 10 = 60 := by
    rw [Finset.sum_eq_single 3]
    · decide
    · intro k hk h3
      have := (capRun_frame hrun (capRange_ne_pool hk)
        (by simp [capCmPendingLs, CapLabel.chain?, Ne.symm h3])).2.2.1
      rw [this]; rfl
    · intro h; exact absurd (Finset.mem_range.mpr (by decide)) h
  refine ⟨capDemoStart 100 true, capCmPendingS, capCmPendingT, capCmPendingLs, 3, 2, 10, 12, 100,
    capDemoStart_upgrade true (by decide), hrun, by decide, by decide, ?_, by decide, by decide,
    by decide, by decide, by decide, Option.isSome_iff_exists.mp (by decide), by decide, by decide,
    hstep, by decide, by decide, by decide, by decide, Option.isNone_iff_eq_none.mp (by decide),
    by decide, ?_⟩
  · rw [hsum]; decide
  · intro y hy
    have hk : capTrackedKey deployedCapConfig capCmPendingS 2 (capCmPendingS.origin 12) = some 2 := by
      decide
    refine ⟨_, capStep_fromChain.mpr ⟨⟨by decide, hy, fun h => absurd h (by decide),
      fun k hk' => ?_⟩, rfl⟩⟩
    rw [hk] at hk'
    cases hk'
    have hw0 : capCmPendingS.withdrawn 2 12 = 0 := by decide
    exact ⟨by rw [hw0]; simpa using hy, fun h => absurd h (by decide)⟩

/-! ### Countermodel (2) -/

/-- Chain 2 gets a backfill of 40 and, still pending, withdraws 50; then (`capCmDeficitT`) it is
marked backfilled. -/
def capCmDeficitLs : List CapLabel := [.setBackfill 2 10 40, .fromChain 2 10 50]

def capCmDeficitS : CapState :=
  (capExec deployedCapConfig (capDemoStart 100 true) capCmDeficitLs).getD (capDemoStart 100 true)

def capCmDeficitT : CapState :=
  (capStep deployedCapConfig (.markBackfilled 2) capCmDeficitS).getD capCmDeficitS

theorem BulkheadMarkBackfilledKeepsDeficit : Properties.BulkheadMarkBackfilledKeepsDeficit := by
  refine ⟨fun cfg s c h => capStep_markBackfilled.mpr ⟨h, rfl⟩, ?_⟩
  have hrun : CapRun deployedCapConfig (capDemoStart 100 true) capCmDeficitLs capCmDeficitS :=
    capRun_of_exec (capOption_getD (by decide))
  have hstep : capStep deployedCapConfig (.markBackfilled 2) capCmDeficitS = some capCmDeficitT :=
    capOption_getD (by decide)
  refine ⟨capDemoStart 100 true, capCmDeficitS, capCmDeficitT, capCmDeficitLs, 2, 10,
    capDemoStart_upgrade true (by decide), hrun, by decide, by decide, by decide, by decide,
    by decide, by decide, hstep, ?_, ?_⟩
  · intro x
    by_contra hne
    obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hne
    obtain ⟨⟨-, -, -, hallow⟩, -⟩ := capStep_fromChain.mp hu
    have hk : capTrackedKey deployedCapConfig capCmDeficitT 2 (capCmDeficitT.origin 10) = some 2 := by
      decide
    have := ((hallow 2 hk).2 (by decide)).2
    have e1 : capCmDeficitT.withdrawn 2 10 = 50 := by decide
    have e2 : capCmDeficitT.deposited 2 10 = 0 := by decide
    have e3 : capCmDeficitT.backfill 2 10 = 40 := by decide
    omega
  · intro ls' t' hr' hti hto
    have hb := BulkheadDisabledChainReleaseBound deployedCapConfig capCmDeficitT t' ls' 2 10 hr'
      (by decide) (by decide) hti (by decide) (by decide) hto
    exact ⟨hb.2.1, (capRun_mono hr').2.2.2.2.2.1 2 10 (by decide)⟩

/-! ### Witness for the cap statements -/

/-- Both chains get their backfills (40 and 60) and are marked; chain 2 gets interop. -/
def capWitLs : List CapLabel :=
  [.setBackfill 2 10 40, .setBackfill 3 10 60, .markBackfilled 2, .markBackfilled 3,
    .enableInterop 2]

/-- Chain 2's balance moves to the pool; chain 3 receives 5; chain 2 withdraws 40 from the pool;
chain 3 receives 7 of asset 11 (native to chain 2).  Then (`capWitT`) chain 3 withdraws 65. -/
def capWitLs' : List CapLabel :=
  [.moveToPool 2 10, .toChain 3 10 5, .fromChain 2 10 40, .toChain 3 11 7]

def capWitS : CapState :=
  (capExec deployedCapConfig (capDemoStart 100 true) capWitLs).getD (capDemoStart 100 true)

def capWitU : CapState := (capExec deployedCapConfig capWitS capWitLs').getD capWitS

def capWitT : CapState := (capStep deployedCapConfig (.fromChain 3 10 65) capWitU).getD capWitU

theorem BulkheadCapWitness : Properties.BulkheadCapWitness := by
  have h0 := capDemoStart_upgrade true (b0 := 100) (by decide)
  have hrun : CapRun deployedCapConfig (capDemoStart 100 true) capWitLs capWitS :=
    capRun_of_exec (capOption_getD (by decide))
  have hrun' : CapRun deployedCapConfig capWitS capWitLs' capWitU :=
    capRun_of_exec (capOption_getD (by decide))
  have hstep : capStep deployedCapConfig (.fromChain 3 10 65) capWitU = some capWitT :=
    capOption_getD (by decide)
  have hframe := capStep_frame hstep (d := 2) (by decide) (by decide)
  refine ⟨capDemoStart 100 true, capWitS, capWitU, capWitT, capWitLs, capWitLs', 3, 2, 2, 10, 11, 65,
    h0, hrun, capRun_snoc hrun' hstep, hrun', hstep, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, hframe.2.2.1, hframe.1,
    BulkheadRunsStayWellFormed _ _ _ _ deployedCapConfig_ok h0 hrun, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    Option.isSome_iff_exists.mp (by decide)⟩

/-! ### Witness for the ledger statements -/

/-- From `bridgedOut = 30`: population of 70, backfills 40 and 60, both marked, chain 2 enabled
and moved, a deposit of 5 to chain 3, withdrawals of 20 by chain 3 and 15 by chain 2. -/
def capLedLs : List CapLabel :=
  [.populate 10 70, .setBackfill 2 10 40, .setBackfill 3 10 60, .markBackfilled 2,
    .markBackfilled 3, .enableInterop 2, .moveToPool 2 10, .toChain 3 10 5, .fromChain 3 10 20,
    .fromChain 2 10 15]

def capLedS : CapState :=
  (capExec deployedCapConfig (capDemoStart 30 false) capLedLs).getD (capDemoStart 30 false)

theorem capLedS_frame {k : ℕ} (hk2 : k ≠ 2) (hk3 : k ≠ 3) (hkp : k ≠ deployedCapConfig.pool) :
    capLedS.deposited k = (capDemoStart 30 false).deposited k ∧
      capLedS.withdrawn k = (capDemoStart 30 false).withdrawn k ∧
      capLedS.backfill k = (capDemoStart 30 false).backfill k ∧
      capLedS.inPool k = (capDemoStart 30 false).inPool k ∧
      capLedS.pending k = (capDemoStart 30 false).pending k :=
  capRun_frame (capRun_of_exec (capOption_getD (by decide))) hkp
    (by simp [capLedLs, CapLabel.chain?, Ne.symm hk2, Ne.symm hk3])

theorem BulkheadLedgerWitness : Properties.BulkheadLedgerWitness := by
  have h0 := capDemoStart_upgrade false (b0 := 30) (by decide)
  have hrun : CapRun deployedCapConfig (capDemoStart 30 false) capLedLs capLedS :=
    capRun_of_exec (capOption_getD (by decide))
  have h2mem : (2 : ℕ) ∈ range chainIdCap := Finset.mem_range.mpr (by decide)
  have h3mem : (3 : ℕ) ∈ range chainIdCap := Finset.mem_range.mpr (by decide)
  have hbf : ∑ k ∈ range chainIdCap, capLedS.backfill k 10 = 100 := by
    rw [capSum_pair h2mem h3mem (by decide) (fun k hk h2 h3 => by
      rw [(capLedS_frame h2 h3 (capRange_ne_pool hk)).2.2.1]; rfl)]
    decide
  have hunmoved : ∑ k ∈ range chainIdCap,
      (if capLedS.inPool k 10 = true then 0 else capHeadroom capLedS k 10)
        + capHeadroom capLedS deployedCapConfig.pool 10 = (capLedS.bridgedOut 10 : ℤ) := by
    rw [capSum_pair h2mem h3mem (by decide) (fun k hk h2 h3 => by
      obtain ⟨e1, e2, e3, e4, -⟩ := capLedS_frame h2 h3 (capRange_ne_pool hk)
      simp only [capHeadroom, e1, e2, e3, e4]
      simp [capDemoStart])]
    decide
  refine ⟨capDemoStart 30 false, capLedS, capLedLs, 10, 3, 2, h0, hrun, by decide, by decide,
    by decide, by rw [hbf]; decide, by rw [hbf]; decide, by decide, by decide, by decide, ?_, ?_,
    hunmoved, by decide, by decide, by decide, by decide, by decide,
    Option.isSome_iff_exists.mp (by decide)⟩
  · intro k
    by_cases h2 : k = 2
    · subst h2; decide
    by_cases h3 : k = 3
    · subst h3; decide
    by_cases hp : k = deployedCapConfig.pool
    · rw [hp]; decide
    rw [(capLedS_frame h2 h3 hp).2.2.2.2]
    simp [capDemoStart, h2, h3]
  · intro k
    by_cases h2 : k = 2
    · subst h2; decide
    by_cases h3 : k = 3
    · subst h3; decide
    by_cases hp : k = deployedCapConfig.pool
    · rw [hp]; decide
    obtain ⟨e1, e2, e3, -, -⟩ := capLedS_frame h2 h3 hp
    simp only [capHeadroom, e1, e2, e3]
    simp [capDemoStart]

end Contracts.L1NativeTokenVault.Bulkhead
