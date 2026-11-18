import EraSpec.Contracts.L1NativeTokenVault.Properties.BulkheadPoolSimulation
import EraSpec.Contracts.L1NativeTokenVault.Proofs.BulkheadIsolation
import EraSpec.Contracts.L1NativeTokenVault.Proofs.InteropPool

/-!
# Proofs: the bulkhead model's runs are `InteropPool` runs

Proofs of `EraSpec.Contracts.L1NativeTokenVault.Properties.BulkheadPoolSimulation`.

Each case of `capStep_poolCall` takes the guards a successful bulkhead call passed (the closed
forms `capStep_toChain`, … of `Proofs/BulkheadIsolationSteps.lean`), reads them at word indices
through `CapPoolCorr`, discharges the `InteropPool` function's guards with them, and checks the two
results field by field.  On words, `_trackedBalance` agrees (`capTracked_none`, `capTracked_some`),
and `setAt`/`setAt2` agree with `Function.update`/`capUpd2` (`capSetAt_corr`, `capSetAt2_corr`).
-/

namespace Contracts.L1NativeTokenVault.Bulkhead

/-! ## Words -/

theorem capWordBound_eq_size : capWordBound = UInt256.size := by
  unfold capWordBound UInt256.size; norm_num

theorem capWord_val {n : ℕ} (h : n < capWordBound) : (capWord n).val = n :=
  Nat.mod_eq_of_lt (capWordBound_eq_size ▸ h)

theorem capWord_eq_iff {n : ℕ} (h : n < capWordBound) {u : UInt256} :
    capWord n = u ↔ n = u.val := by
  constructor
  · rintro rfl; exact (capWord_val h).symm
  · intro e; exact Fin.ext (by rw [capWord_val h, e])

theorem capWord_inj {m n : ℕ} (hm : m < capWordBound) (hn : n < capWordBound) :
    capWord m = capWord n ↔ m = n := by
  rw [capWord_eq_iff hm, capWord_val hn]

theorem capUInt_lt (u : UInt256) : u.val < capWordBound := by
  rw [capWordBound_eq_size]; exact u.isLt

theorem CapLabel.Words.get {l : CapLabel} (hw : l.Words) {n : ℕ} (hn : n ∈ l.nums) :
    n < capWordBound := hw n hn

/-! ## Pointwise updates -/

theorem capSetAt_corr {β : Type} {f : UInt256 → β} {g : ℕ → β} (h : ∀ u, f u = g u.val)
    (k : UInt256) (v : β) (u : UInt256) :
    InteropPool.setAt f k v u = Function.update g k.val v u.val := by
  rw [InteropPool.setAt_apply, Function.update_apply]
  by_cases hu : u = k
  · subst hu; simp
  · have hv : u.val ≠ k.val := fun e => hu (Fin.ext e)
    rw [capIte_neg hu, capIte_neg hv, h]

theorem capSetAt2_corr {β : Type} {f : UInt256 → UInt256 → β} {g : ℕ → ℕ → β}
    (h : ∀ c a, f c a = g c.val a.val) (k a : UInt256) (v : β) (c' a' : UInt256) :
    InteropPool.setAt2 f k a v c' a' = capUpd2 g k.val a.val v c'.val a'.val := by
  rw [InteropPool.setAt2_apply, capUpd2_apply]
  by_cases hc : c' = k
  · subst hc
    by_cases ha : a' = a
    · subst ha; simp
    · have hv : a'.val ≠ a.val := fun e => ha (Fin.ext e)
      rw [capIte_neg (fun h' => ha h'.2), capIte_neg (fun h' => hv h'.2), h]
  · have hv : c'.val ≠ k.val := fun e => hc (Fin.ext e)
    rw [capIte_neg (fun h' => hc h'.1), capIte_neg (fun h' => hv h'.1), h]

/-! ## `_trackedBalance` on words -/

theorem capTracked_none {cfg : CapConfig} {s : CapState} {p : InteropPool.PoolSys}
    (hc : CapPoolCorr s p) {c o : ℕ} (hcB : c < capWordBound) (hoB : o < capWordBound)
    (hk : capTrackedKey cfg s c o = none) :
    (InteropPool.trackedBalance p (capWord c) (capWord o)).1 = false := by
  unfold capTrackedKey at hk
  unfold InteropPool.trackedBalance
  rw [hc.interop, hc.interop, capWord_val hcB, capWord_val hoB]
  by_cases h1 : s.interop c = true
  · rw [capIte_pos h1] at hk
    by_cases h2 : s.interop o = true
    · simp [h1, h2]
    · rw [capIte_neg h2] at hk; cases hk
  · rw [capIte_neg h1] at hk
    by_cases h3 : o = c
    · subst h3; simp [h1]
    · rw [capIte_neg h3] at hk; cases hk

theorem capTracked_some {cfg : CapConfig} {s : CapState} {p : InteropPool.PoolSys}
    (hc : CapPoolCorr s p) (hpool : cfg.pool = InteropPool.interopPoolChainId.val) {c o k : ℕ}
    (hcB : c < capWordBound) (hoB : o < capWordBound) (hk : capTrackedKey cfg s c o = some k) :
    (InteropPool.trackedBalance p (capWord c) (capWord o)).1 = true ∧
      (InteropPool.trackedBalance p (capWord c) (capWord o)).2.val = k := by
  unfold capTrackedKey at hk
  unfold InteropPool.trackedBalance
  rw [hc.interop, hc.interop, capWord_val hcB, capWord_val hoB]
  by_cases h1 : s.interop c = true
  · rw [capIte_pos h1] at hk
    by_cases h2 : s.interop o = true
    · rw [capIte_pos h2] at hk; cases hk
    · rw [capIte_neg h2] at hk
      cases hk
      simp [h1, h2, hpool]
  · rw [capIte_neg h1] at hk
    by_cases h3 : o = c
    · rw [capIte_pos h3] at hk; cases hk
    · rw [capIte_neg h3] at hk
      cases hk
      have hne : capWord o ≠ capWord c := fun e => h3 ((capWord_inj hoB hcB).mp e)
      simp [h1, hne, capWord_val hcB]

/-! ## One call -/

/-- The correspondence for a result that changes only `bridgedOut` on the `InteropPool` side and
the bulkhead side. -/
theorem capCorr_bridgedOut {s : CapState} {p : InteropPool.PoolSys} (hc : CapPoolCorr s p)
    {f : UInt256 → ℕ} {g : ℕ → ℕ} (h : ∀ a, f a = g a.val) :
    CapPoolCorr { s with bridgedOut := g } { p with bridgedOut := f } :=
  { hc with bridgedOut := h }

theorem capStep_poolCall {cfg : CapConfig} {l1 : UInt256} {s t : CapState}
    {p : InteropPool.PoolSys} {l : CapLabel} (hm : cfg.MatchesPool l1) (hc : CapPoolCorr s p)
    (hw : l.Words) (h : capStep cfg l s = some t) :
    match l.toPoolCall s with
    | none => CapPoolCorr t p
    | some call => ∃ p', InteropPool.poolCall l1 call p = some p' ∧ CapPoolCorr t p' := by
  cases l with
  | toChain c a x =>
    obtain ⟨⟨-, hx, hbo, hdep⟩, rfl⟩ := capStep_toChain.mp h
    have hcB : c < capWordBound := hw.get (by simp [CapLabel.nums])
    have haB : a < capWordBound := hw.get (by simp [CapLabel.nums])
    have hoB := hc.origin_lt a
    have hO : capWord (s.origin a) = l1 ↔ s.origin a = cfg.l1 := by
      rw [capWord_eq_iff hoB, hm.1]
    have hB : p.bridgedOut (capWord a) = s.bridgedOut a := by rw [hc.bridgedOut, capWord_val haB]
    have hX : (capWord x).val = x := capWord_val hx
    show ∃ p', InteropPool.handleBridgeToChain l1 p (capWord c) (capWord a) (capWord x)
      (capWord (s.origin a)) = some p' ∧ _
    have hbo' : ∀ a', (if capWord (s.origin a) = l1 then
          InteropPool.setAt p.bridgedOut (capWord a) (p.bridgedOut (capWord a) + (capWord x).val)
        else p.bridgedOut) a' = (toChainPost cfg s c a x).bridgedOut a'.val := by
      intro a'
      simp only [toChainPost]
      by_cases ho : s.origin a = cfg.l1
      · rw [capIte_pos (hO.mpr ho), capIte_pos ho, hB, hX, capSetAt_corr hc.bridgedOut, capWord_val haB]
      · rw [capIte_neg (mt hO.mp ho), capIte_neg ho, hc.bridgedOut]
    unfold InteropPool.handleBridgeToChain
    have h1 : ¬(capWord (s.origin a) = l1 ∧
        UInt256.size ≤ p.bridgedOut (capWord a) + (capWord x).val) := by
      rintro ⟨e, hle⟩
      rw [hB, hX, ← capWordBound_eq_size] at hle
      have := hbo (hO.mp e); omega
    rw [capIte_neg h1]
    dsimp only
    rcases hk : capTrackedKey cfg s c (s.origin a) with _ | k
    · have ht := capTracked_none hc hcB hoB hk
      rw [capIte_neg (by simp [ht])]
      refine ⟨_, rfl, { hc with bridgedOut := hbo', deposited := ?_ }⟩
      intro c' a'
      simp only [toChainPost, hk, capBump_none]
      exact hc.deposited c' a'
    · obtain ⟨ht1, ht2⟩ := capTracked_some hc hm.2 hcB hoB hk
      rw [capIte_pos ht1]
      have hD : p.deposited (InteropPool.trackedBalance p (capWord c) (capWord (s.origin a))).2
          (capWord a) = s.deposited k a := by rw [hc.deposited, ht2, capWord_val haB]
      have hlt := hdep k hk
      rw [capIte_neg (by rw [hD, hX, ← capWordBound_eq_size]; omega)]
      refine ⟨_, rfl, { hc with bridgedOut := hbo', deposited := ?_ }⟩
      intro c' a'
      simp only [toChainPost, hk, capBump_some]
      rw [hD, hX, capSetAt2_corr hc.deposited, ht2, capWord_val haB]
  | fromChain c a x =>
    obtain ⟨⟨-, hx, hbo, hallow⟩, rfl⟩ := capStep_fromChain.mp h
    have hcB : c < capWordBound := hw.get (by simp [CapLabel.nums])
    have haB : a < capWordBound := hw.get (by simp [CapLabel.nums])
    have hoB := hc.origin_lt a
    have hO : capWord (s.origin a) = l1 ↔ s.origin a = cfg.l1 := by
      rw [capWord_eq_iff hoB, hm.1]
    have hB : p.bridgedOut (capWord a) = s.bridgedOut a := by rw [hc.bridgedOut, capWord_val haB]
    have hX : (capWord x).val = x := capWord_val hx
    show ∃ p', InteropPool.handleBridgeFromChain l1 p (capWord c) (capWord a) (capWord x)
      (capWord (s.origin a)) = some p' ∧ _
    have hbo' : ∀ a', (if capWord (s.origin a) = l1 then
          InteropPool.setAt p.bridgedOut (capWord a) (p.bridgedOut (capWord a) - (capWord x).val)
        else p.bridgedOut) a' = (fromChainPost cfg s c a x).bridgedOut a'.val := by
      intro a'
      simp only [fromChainPost]
      by_cases ho : s.origin a = cfg.l1
      · rw [capIte_pos (hO.mpr ho), capIte_pos ho, hB, hX, capSetAt_corr hc.bridgedOut, capWord_val haB]
      · rw [capIte_neg (mt hO.mp ho), capIte_neg ho, hc.bridgedOut]
    unfold InteropPool.handleBridgeFromChain
    have h1 : ¬(capWord (s.origin a) = l1 ∧ p.bridgedOut (capWord a) < (capWord x).val) := by
      rintro ⟨e, hlt⟩
      rw [hB, hX] at hlt
      have := hbo (hO.mp e); omega
    rw [capIte_neg h1]
    dsimp only
    rcases hk : capTrackedKey cfg s c (s.origin a) with _ | k
    · have ht := capTracked_none hc hcB hoB hk
      rw [capIte_neg (by simp [ht])]
      refine ⟨_, rfl, { hc with bridgedOut := hbo', withdrawn := ?_ }⟩
      intro c' a'
      simp only [fromChainPost, hk, capBump_none]
      exact hc.withdrawn c' a'
    · obtain ⟨ht1, ht2⟩ := capTracked_some hc hm.2 hcB hoB hk
      rw [capIte_pos ht1]
      set key := (InteropPool.trackedBalance p (capWord c) (capWord (s.origin a))).2 with hkey
      have hW : p.withdrawn key (capWord a) = s.withdrawn k a := by
        rw [hc.withdrawn, ht2, capWord_val haB]
      have hD : p.deposited key (capWord a) = s.deposited k a := by
        rw [hc.deposited, ht2, capWord_val haB]
      have hF : p.backfill key (capWord a) = s.backfill k a := by
        rw [hc.backfill, ht2, capWord_val haB]
      have hP : p.pending key = s.pending k := by rw [hc.pending, ht2]
      obtain ⟨hw1, hw2⟩ := hallow k hk
      rw [capIte_neg (by rw [hW, hX, ← capWordBound_eq_size]; omega)]
      rw [capIte_neg (by
        rw [hP, hD, hF, hW, hX, ← capWordBound_eq_size]
        rintro ⟨hp, hor⟩
        have := hw2 hp
        omega)]
      refine ⟨_, rfl, { hc with bridgedOut := hbo', withdrawn := ?_ }⟩
      intro c' a'
      simp only [fromChainPost, hk, capBump_some]
      rw [hW, hX, capSetAt2_corr hc.withdrawn, ht2, capWord_val haB]
  | setBackfill c a v =>
    obtain ⟨⟨hcp, hv, hz, hin⟩, rfl⟩ := capStep_setBackfill.mp h
    have hcB : c < capWordBound := hw.get (by simp [CapLabel.nums])
    have haB : a < capWordBound := hw.get (by simp [CapLabel.nums])
    have hV : (capWord v).val = v := capWord_val hv
    have hpw : capWord c ≠ InteropPool.interopPoolChainId := by
      intro e; exact hcp (by rw [hm.2, ← (capWord_eq_iff hcB).mp e])
    have hZ : p.backfill (capWord c) (capWord a) = 0 := by
      rw [hc.backfill, capWord_val hcB, capWord_val haB, hz]
    have hI : p.inPool (capWord c) (capWord a) = s.inPool c a := by
      rw [hc.inPool, capWord_val hcB, capWord_val haB]
    have hD : p.deposited (capWord c) (capWord a) = s.deposited c a := by
      rw [hc.deposited, capWord_val hcB, capWord_val haB]
    have hW : p.withdrawn (capWord c) (capWord a) = s.withdrawn c a := by
      rw [hc.withdrawn, capWord_val hcB, capWord_val haB]
    have hPD : p.deposited InteropPool.interopPoolChainId (capWord a) = s.deposited cfg.pool a := by
      rw [hc.deposited, capWord_val haB, hm.2]
    have hbf : ∀ c' a', InteropPool.setAt2 p.backfill (capWord c) (capWord a) v c' a'
        = (setBackfillPost cfg s c a v).backfill c'.val a'.val := by
      intro c' a'
      simp only [setBackfillPost]
      rw [capSetAt2_corr hc.backfill, capWord_val hcB, capWord_val haB]
    show ∃ p', InteropPool.setChainBalanceBackfill p (capWord c) (capWord a) (capWord v) = some p'
      ∧ _
    unfold InteropPool.setChainBalanceBackfill
    rw [capIte_neg hpw, capIte_neg (by simp [hZ]), hV]
    by_cases hp : s.inPool c a = true
    · rw [capIte_pos (by rw [hI, hp])]
      obtain ⟨hdv, hcred⟩ := hin hp
      rw [capIte_neg (by rw [hD, ← capWordBound_eq_size]; omega)]
      dsimp only
      simp only [InteropPool.netOf_eq, Nat.add_zero]
      rw [hD, hW]
      rw [capIte_neg (by omega)]
      rw [capIte_neg (by rw [hPD, ← capWordBound_eq_size]; unfold setBackfillCredit at hcred; omega)]
      refine ⟨_, rfl, { hc with deposited := ?_, backfill := hbf }⟩
      intro c' a'
      simp only [setBackfillPost, capIte_pos hp, setBackfillCredit]
      rw [hPD, capSetAt2_corr hc.deposited, capWord_val haB, hm.2]
    · rw [capIte_neg (by rw [hI]; exact hp)]
      refine ⟨_, rfl, { hc with deposited := ?_, backfill := hbf }⟩
      intro c' a'
      simp only [setBackfillPost, capIte_neg hp]
      exact hc.deposited c' a'
  | markBackfilled c =>
    obtain ⟨hp, rfl⟩ := capStep_markBackfilled.mp h
    have hcB : c < capWordBound := hw.get (by simp [CapLabel.nums])
    show ∃ p', InteropPool.markBackfilled p (capWord c) = some p' ∧ _
    unfold InteropPool.markBackfilled
    rw [capIte_pos (by rw [hc.pending, capWord_val hcB, hp])]
    refine ⟨_, rfl, { hc with pending := ?_ }⟩
    intro c'
    dsimp only
    rw [capSetAt_corr hc.pending, capWord_val hcB]
  | moveToPool c a =>
    obtain ⟨⟨hi, hp, hin, hdb, hcred⟩, rfl⟩ := capStep_moveToPool.mp h
    have hcB : c < capWordBound := hw.get (by simp [CapLabel.nums])
    have haB : a < capWordBound := hw.get (by simp [CapLabel.nums])
    have hD : p.deposited (capWord c) (capWord a) = s.deposited c a := by
      rw [hc.deposited, capWord_val hcB, capWord_val haB]
    have hW : p.withdrawn (capWord c) (capWord a) = s.withdrawn c a := by
      rw [hc.withdrawn, capWord_val hcB, capWord_val haB]
    have hF : p.backfill (capWord c) (capWord a) = s.backfill c a := by
      rw [hc.backfill, capWord_val hcB, capWord_val haB]
    have hPD : p.deposited InteropPool.interopPoolChainId (capWord a) = s.deposited cfg.pool a := by
      rw [hc.deposited, capWord_val haB, hm.2]
    show ∃ p', InteropPool.moveChainBalanceToInteropPool p (capWord c) (capWord a) = some p' ∧ _
    unfold InteropPool.moveChainBalanceToInteropPool
    rw [capIte_neg (by rw [hc.interop, capWord_val hcB, hi]; simp),
      capIte_neg (by rw [hc.pending, capWord_val hcB, hp]; simp),
      capIte_neg (by rw [hc.inPool, capWord_val hcB, capWord_val haB, hin]; simp),
      capIte_neg (by rw [hD, hF, ← capWordBound_eq_size]; omega)]
    dsimp only
    simp only [InteropPool.netOf_eq]
    rw [hD, hF, hW, hPD]
    rw [capIte_neg (by rw [← capWordBound_eq_size]; unfold moveCredit at hcred; omega)]
    refine ⟨_, rfl, { hc with inPool := ?_, deposited := ?_ }⟩
    · intro c' a'
      simp only [movePost, moveCredit]
      rw [capSetAt2_corr hc.deposited, capWord_val haB, ← hm.2]
    · intro c' a'
      simp only [movePost]
      rw [capSetAt2_corr hc.inPool, capWord_val hcB, capWord_val haB]
  | initializeUpgrade =>
    obtain ⟨hu, rfl⟩ := capStep_initializeUpgrade.mp h
    show ∃ p', InteropPool.initializeUpgrade p = some p' ∧ _
    unfold InteropPool.initializeUpgrade
    have hv : p.initVersion < 2 := by
      by_contra hge
      have := hc.upgraded.mp (by omega)
      rw [hu] at this; cases this
    rw [capIte_pos hv]
    refine ⟨_, rfl, { hc with pending := ?_, upgraded := ?_ }⟩
    · intro c'
      simp only
      rw [hc.pending, hc.registered, Bool.or_comm]
    · simp
  | enableInterop c =>
    obtain ⟨⟨hr, hi, hp⟩, rfl⟩ := capStep_enableInterop.mp h
    have hcB : c < capWordBound := hw.get (by simp [CapLabel.nums])
    show ∃ p', InteropPool.enableInterop p (capWord c) = some p' ∧ _
    unfold InteropPool.enableInterop
    rw [capIte_neg (by rw [hc.registered, capWord_val hcB, hr]; simp),
      capIte_neg (by rw [hc.interop, capWord_val hcB, hi]; simp),
      capIte_neg (by rw [hc.pending, capWord_val hcB, hp]; simp)]
    refine ⟨_, rfl, { hc with interop := ?_ }⟩
    intro c'
    dsimp only
    rw [capSetAt_corr hc.interop, capWord_val hcB]
  | registerChain c =>
    obtain ⟨⟨h0, hcap, hl1, hr⟩, rfl⟩ := capStep_registerChain.mp h
    have hcB : c < capWordBound := hw.get (by simp [CapLabel.nums])
    show ∃ p', InteropPool.registerChain l1 p (capWord c) = some p' ∧ _
    unfold InteropPool.registerChain
    rw [capIte_neg (by
      rw [capWord_val hcB, hc.registered, capWord_val hcB, hr, capWord_eq_iff hcB, ← hm.1]
      have : InteropPool.chainIdCap = chainIdCap := rfl
      rw [this]
      rintro (e | e | e | e)
      · exact h0 e
      · omega
      · exact hl1 e
      · cases e)]
    refine ⟨_, rfl, { hc with registered := ?_ }⟩
    intro c'
    dsimp only
    rw [capSetAt_corr hc.registered, capWord_val hcB]
  | registerAsset a o =>
    obtain ⟨⟨-, -⟩, rfl⟩ := capStep_registerAsset.mp h
    have hoB : o < capWordBound := hw.get (by simp [CapLabel.nums])
    show CapPoolCorr _ p
    refine { hc with origin_lt := ?_ }
    intro a'
    simp only [Function.update_apply]
    split_ifs
    · exact hoB
    · exact hc.origin_lt a'
  | populate a L =>
    obtain ⟨⟨-, -, hlt⟩, rfl⟩ := capStep_populate.mp h
    have haB : a < capWordBound := hw.get (by simp [CapLabel.nums])
    have hLB : L < capWordBound := hw.get (by simp [CapLabel.nums])
    have hB : p.bridgedOut (capWord a) = s.bridgedOut a := by rw [hc.bridgedOut, capWord_val haB]
    show ∃ p', InteropPool.populateBridgedOutEntry p (capWord a) (capWord L) = some p' ∧ _
    unfold InteropPool.populateBridgedOutEntry
    rw [capIte_neg (by rw [hB, capWord_val hLB, ← capWordBound_eq_size]; omega)]
    refine ⟨_, rfl, { hc with bridgedOut := ?_ }⟩
    intro a'
    simp only
    rw [hB, capWord_val hLB, capSetAt_corr hc.bridgedOut, capWord_val haB]

theorem BulkheadStepIsPoolCall : Properties.BulkheadStepIsPoolCall := by
  intro cfg l1 s t p l hm hc hw h
  have hsim := capStep_poolCall hm hc hw h
  refine ⟨fun call hl => ?_, fun hl => ?_⟩
  · rw [hl] at hsim; exact hsim
  · rw [hl] at hsim; exact hsim

/-! ## Runs -/

theorem capRun_poolRun {cfg : CapConfig} {l1 : UInt256} (hm : cfg.MatchesPool l1)
    {s t : CapState} {ls : List CapLabel} (hr : CapRun cfg s ls t) :
    ∀ {p : InteropPool.PoolSys}, CapPoolCorr s p → (∀ l ∈ ls, l.Words) →
      ∃ p', InteropPool.PoolRun l1 p (capPoolCalls cfg s ls) p' ∧ CapPoolCorr t p' := by
  induction hr with
  | nil s => intro p hc _; exact ⟨p, InteropPool.PoolRun.nil p, hc⟩
  | @cons s u t l ls hs hr ih =>
    intro p hc hw
    have hsim := capStep_poolCall hm hc (hw l List.mem_cons_self) hs
    have hw' : ∀ l' ∈ ls, l'.Words := fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    have hcalls : capPoolCalls cfg s (l :: ls) = (l.toPoolCall s).toList ++ capPoolCalls cfg u ls := by
      simp only [capPoolCalls, hs]
    rw [hcalls]
    cases hl : l.toPoolCall s with
    | none =>
      rw [hl] at hsim
      obtain ⟨p', hr', hc'⟩ := ih hsim hw'
      exact ⟨p', by simpa using hr', hc'⟩
    | some call =>
      rw [hl] at hsim
      obtain ⟨pm, hpm, hcm⟩ := hsim
      obtain ⟨p', hr', hc'⟩ := ih hcm hw'
      exact ⟨p', InteropPool.PoolRun.cons hpm hr', hc'⟩

theorem BulkheadRunIsPoolRun : Properties.BulkheadRunIsPoolRun :=
  fun _ _ _ _ _ _ hm hc hw hr => capRun_poolRun hm hr hc hw

/-! ## The upgrade state -/

/-- The `InteropPool` state just before the upgrade that a bulkhead upgrade state comes from: its
storage at word indices, nothing pending, version 1, no ghost. -/
def capPreOf (s0 : CapState) : InteropPool.PoolSys where
  bridgedOut := fun a => s0.bridgedOut a.val
  deposited := fun c a => s0.deposited c.val a.val
  withdrawn := fun c a => s0.withdrawn c.val a.val
  backfill := fun c a => s0.backfill c.val a.val
  inPool := fun c a => s0.inPool c.val a.val
  pending := fun _ => false
  initVersion := 1
  interop := fun c => s0.interop c.val
  registered := fun c => s0.registered c.val
  directToPool := fun _ => 0

theorem capPreOf_preUpgrade {cfg : CapConfig} {s0 : CapState} (h : CapUpgradeState cfg s0) :
    InteropPool.PreUpgrade (capPreOf s0) where
  version := by show 1 < 2; decide
  noInterop := fun c => h.interop_false c.val
  noneInPool := fun c a => h.inPool_false c.val a.val
  pendingRegistered := fun _ e => by cases e
  poolUnregistered := by
    show s0.registered InteropPool.interopPoolChainId.val = false
    cases hr : s0.registered InteropPool.interopPoolChainId.val
    · rfl
    · have := (h.registered_valid _ hr).2.1
      have := InteropPool.pool_above_cap
      have e : InteropPool.chainIdCap = chainIdCap := rfl
      omega
  poolDepositedZero := fun a => h.deposited_zero _ _
  poolWithdrawnZero := fun a => h.withdrawn_zero _ _
  poolBackfillZero := fun a => h.backfill_zero _ _
  noDirect := fun _ => rfl

theorem capPreOf_initializeUpgrade {cfg : CapConfig} {s0 : CapState} (h : CapUpgradeState cfg s0)
    (ho : ∀ a, s0.origin a < capWordBound) :
    ∃ p0, InteropPool.initializeUpgrade (capPreOf s0) = some p0 ∧ CapPoolCorr s0 p0 := by
  refine ⟨_, capIte_pos (show (capPreOf s0).initVersion < 2 by show 1 < 2; decide) _ _, ?_⟩
  exact
    { bridgedOut := fun _ => rfl
      deposited := fun _ _ => rfl
      withdrawn := fun _ _ => rfl
      backfill := fun _ _ => rfl
      inPool := fun _ _ => rfl
      pending := fun c => by
        show (false || s0.registered c.val) = s0.pending c.val
        rw [h.pending_eq, Bool.false_or]
      interop := fun _ => rfl
      registered := fun _ => rfl
      upgraded := by simp [h.upgraded]
      origin_lt := ho }

theorem BulkheadUpgradeStateIsPostUpgrade : Properties.BulkheadUpgradeStateIsPostUpgrade := by
  intro cfg s0 h ho
  obtain ⟨p0, hp0, hc⟩ := capPreOf_initializeUpgrade h ho
  exact ⟨capPreOf s0, p0, capPreOf_preUpgrade h, hp0, hc⟩

theorem BulkheadRunsArePoolRuns : Properties.BulkheadRunsArePoolRuns := by
  intro cfg l1 s0 s ls hm h ho hw hr
  obtain ⟨pre, p0, hpre, hp0, hc0⟩ := BulkheadUpgradeStateIsPostUpgrade cfg s0 h ho
  obtain ⟨p, hrun, hc⟩ := capRun_poolRun hm hr hc0 hw
  exact ⟨pre, p0, p, hpre, hp0, hrun, hc⟩

/-! ## Witness -/

/-- Chain `4` and asset `13` (native to `4`) are registered; 20 of asset `10` is populated; both
chains get their backfills and are marked; chain `2` is enabled and moved; chain `3` receives 5,
chain `2` withdraws 40 from the pool, chain `3` withdraws 65; chain `3` receives and withdraws 7
of asset `13`; chain `4` receives 3 of asset `10`. -/
def capSimLs : List CapLabel :=
  [.registerChain 4, .registerAsset 13 4, .populate 10 20, .setBackfill 2 10 40,
    .setBackfill 3 10 60, .markBackfilled 2, .markBackfilled 3, .enableInterop 2, .moveToPool 2 10,
    .toChain 3 10 5, .fromChain 2 10 40, .fromChain 3 10 65, .toChain 3 13 7, .fromChain 3 13 7,
    .toChain 4 10 3]

def capSimS : CapState :=
  (capExec deployedCapConfig (capDemoStart 100 false) capSimLs).getD (capDemoStart 100 false)

theorem BulkheadPoolSimulationWitness : Properties.BulkheadPoolSimulationWitness := by
  have h0 := capDemoStart_upgrade false (b0 := 100) (by decide)
  have ho : ∀ a, (capDemoStart 100 false).origin a < capWordBound := by
    intro a
    simp only [capDemoStart]
    split_ifs <;> unfold capWordBound <;> norm_num
  have hrun : CapRun deployedCapConfig (capDemoStart 100 false) capSimLs capSimS :=
    capRun_of_exec (capOption_getD (by decide))
  obtain ⟨p0, -, hc0⟩ := capPreOf_initializeUpgrade h0 ho
  exact ⟨capDemoStart 100 false, capSimS, capSimLs, ⟨by decide, by decide⟩, h0, ho, by decide,
    ⟨p0, hc0⟩, hrun, rfl, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

end Contracts.L1NativeTokenVault.Bulkhead
