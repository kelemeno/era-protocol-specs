import EraSpec.Contracts.L1ChainAssetHandler.Specs.SettlementLayerValidation

/-!
# Step lemmas for `SettlementLayerValidation`

Auxiliary to `EraSpec.Contracts.L1ChainAssetHandler.Proofs.SettlementLayerValidation`. It states
and proves the reachable-state invariant `SLVInv` of the model in
`EraSpec.Contracts.L1ChainAssetHandler.Specs.SettlementLayerValidation`.

`SLVInv` is a common part (`SLVCommon`: index 2 is uninitialized, under `sealedOnly` L1 has not
executed any other chain's open batch, the executed log is `1 .. total`, and the L1 diamond's
counter equals L1's message-root counter of `c`) and one of five phases:

* `SLVHome`: `c` settles on L1, `migrationNumber` 0, no message in flight, every executed batch
  on L1;
* `SLVPending t`: burned on L1 towards `t`, the transaction not yet minted (possibly failed);
* `SLVOnSL t`: `c` settles on `t`; the batches after `migrateToGWBatchNumber` ran on `t`;
* `SLVReturning t m`: burned on `t` back to L1 with message `m`, not yet minted on L1;
* `SLVBack t`: back on L1, `migrationNumber` 2, interval 1 closed.

`slvInv_step` proves that every successful step keeps `SLVInv`, in every environment and world;
`slvInv_init` that a start state satisfies it.
-/

namespace Contracts.L1ChainAssetHandler.SettlementLayerValidation

/-! ## Point updates -/

@[simp] lemma upd_self {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) :
    upd f a b a = b := by
  simp [upd]

lemma upd_ne {α β : Type} [DecidableEq α] (f : α → β) {a x : α} (b : β) (h : x ≠ a) :
    upd f a b x = f x := by
  simp [upd, h]

lemma upd_succ_ge (f : ℕ → ℕ) (a x : ℕ) : f x ≤ upd f a (f a + 1) x := by
  by_cases hx : x = a
  · subst hx; simp
  · rw [upd_ne _ _ hx]

lemma upd_some_cases {α : Type} {h : ℕ → Option α} {b x : ℕ} {r r' : α}
    (hx : upd h b (some r) x = some r') : (x = b ∧ r' = r) ∨ (x ≠ b ∧ h x = some r') := by
  by_cases hxb : x = b
  · subst hxb
    simp only [upd_self, Option.some.injEq] at hx
    exact Or.inl ⟨rfl, hx.symm⟩
  · rw [upd_ne _ _ hxb] at hx
    exact Or.inr ⟨hxb, hx⟩

/-- Appending batch `total + 1` to a log that is exactly `1 .. total`. -/
lemma contig_push {hist : ℕ → Option Settled} {total : ℕ}
    (h : ∀ x, (hist x).isSome = true ↔ 1 ≤ x ∧ x ≤ total) (r : Settled) :
    ∀ x, (upd hist (total + 1) (some r) x).isSome = true ↔ 1 ≤ x ∧ x ≤ total + 1 := by
  intro x
  by_cases hx : x = total + 1
  · subst hx; simp
  · rw [upd_ne _ _ hx, h x]; omega

lemma hist_le_total {hist : ℕ → Option Settled} {total : ℕ}
    (h : ∀ x, (hist x).isSome = true ↔ 1 ≤ x ∧ x ≤ total) {x : ℕ} {r : Settled}
    (hx : hist x = some r) : x ≤ total := ((h x).1 (by simp [hx])).2

/-! ## Step inversions -/

lemma step_execL1 {K : ValEnv} {W : ValWorld} {s s' : ValState} {b : ℕ}
    (h : valStep K W s (.execL1 b) = some s') :
    s.awayL1 = false ∧ b = s.mrL1 W.c + 1 ∧ b = s.execL1 + 1 ∧
    s' = { s with mrL1 := upd s.mrL1 W.c b, execL1 := b,
                  hist := upd s.hist b (some ⟨W.l1, 0⟩), total := s.total + 1 } := by
  simp only [valStep] at h
  split_ifs at h with hg
  exact ⟨hg.1, hg.2.1, hg.2.2, (Option.some.inj h).symm⟩

lemma step_execSL {K : ValEnv} {W : ValWorld} {s s' : ValState} {t b : ℕ}
    (h : valStep K W s (.execSL t b) = some s') :
    ∃ g, s.gcopy t = some g ∧ g.active = true ∧ b = g.mr + 1 ∧ b = g.exec + 1 ∧
    s' = { s with gcopy := upd s.gcopy t (some ⟨b, b, true⟩),
                  hist := upd s.hist b (some ⟨t, s.slOpen t⟩), total := s.total + 1 } := by
  simp only [valStep] at h
  split at h
  · rename_i g hg
    split_ifs at h with hc
    exact ⟨g, hg, hc.1, hc.2.1, hc.2.2, (Option.some.inj h).symm⟩
  · simp at h

lemma step_slSeal {K : ValEnv} {W : ValWorld} {s s' : ValState} {t : ℕ}
    (h : valStep K W s (.slSeal t) = some s') :
    s' = { s with slOpen := upd s.slOpen t (s.slOpen t + 1) } := by
  simp only [valStep] at h
  exact (Option.some.inj h).symm

lemma step_slExecL1 {K : ValEnv} {W : ValWorld} {s s' : ValState} {t : ℕ}
    (h : valStep K W s (.slExecL1 t) = some s') :
    t ≠ W.c ∧ t ≠ W.l1 ∧ (K.sealedOnly = true → s.mrL1 t + 1 < s.slOpen t) ∧
    s' = { s with mrL1 := upd s.mrL1 t (s.mrL1 t + 1) } := by
  simp only [valStep] at h
  split_ifs at h with hg
  exact ⟨hg.1, hg.2.1, hg.2.2, (Option.some.inj h).symm⟩

lemma step_burnL1 {K : ValEnv} {W : ValWorld} {s s' : ValState} {t : ℕ}
    (h : valStep K W s (.burnL1 t) = some s') :
    W.enabled = true ∧ W.wl t = true ∧ s.awayL1 = false ∧ W.wl W.c = false ∧
    s.mn < maxMigrations ∧ t ≠ W.l1 ∧ s.mn + 1 = numToSL ∧
    s' = { s with awayL1 := true, mn := s.mn + 1,
                  ivs := upd s.ivs (s.mn + 1) ⟨s.mrL1 W.c, 0, s.mrL1 t, 0, t, true⟩,
                  toSL := some ⟨t, s.mrL1 W.c, s.execL1, s.mn + 1, false⟩ } := by
  simp only [valStep] at h
  split_ifs at h with hg
  exact ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2.1, hg.2.2.2.2.2.2,
    (Option.some.inj h).symm⟩

lemma step_mintSL {K : ValEnv} {W : ValWorld} {s s' : ValState}
    (h : valStep K W s .mintSL = some s') :
    ∃ m, s.toSL = some m ∧ W.enabled = true ∧ m.failed = false ∧
      (s.gcopy m.sl = none ∨
        ∃ g, s.gcopy m.sl = some g ∧ g.mr ≤ m.batchNumber ∧ g.active = false) ∧
      s' = { s with mnG := upd s.mnG m.sl m.num,
                    gcopy := upd s.gcopy m.sl (some ⟨m.exec, m.batchNumber, true⟩),
                    toSL := none } := by
  simp only [valStep] at h
  split at h
  · rename_i m hm
    split_ifs at h with hc
    split at h
    · rename_i hg
      exact ⟨m, hm, hc.1, hc.2, Or.inl hg, (Option.some.inj h).symm⟩
    · rename_i g hg
      split_ifs at h with hc2
      exact ⟨m, hm, hc.1, hc.2, Or.inr ⟨g, hg, hc2.1, hc2.2⟩, (Option.some.inj h).symm⟩
  · simp at h

lemma step_failSL {K : ValEnv} {W : ValWorld} {s s' : ValState}
    (h : valStep K W s .failSL = some s') :
    ∃ m, s.toSL = some m ∧ m.failed = false ∧
      s' = { s with toSL := some { m with failed := true } } := by
  simp only [valStep] at h
  split at h
  · rename_i m hm
    split_ifs at h with hc
    exact ⟨m, hm, hc, (Option.some.inj h).symm⟩
  · simp at h

lemma step_confirmFailure {K : ValEnv} {W : ValWorld} {s s' : ValState}
    (h : valStep K W s .confirmFailure = some s') :
    ∃ m, s.toSL = some m ∧ m.failed = true ∧ s.mn = numToSL ∧ s.awayL1 = true ∧
      s' = { s with mn := s.mn - 1, ivs := upd s.ivs s.mn MigInterval.empty,
                    awayL1 := false, toSL := none } := by
  simp only [valStep] at h
  split at h
  · rename_i m hm
    split_ifs at h with hc
    exact ⟨m, hm, hc.1, hc.2.1, hc.2.2, (Option.some.inj h).symm⟩
  · simp at h

lemma step_burnSL {K : ValEnv} {W : ValWorld} {s s' : ValState} {t : ℕ}
    (h : valStep K W s (.burnSL t) = some s') :
    ∃ g, s.gcopy t = some g ∧ W.enabled = true ∧ g.active = true ∧ s.mnG t < maxMigrations ∧
      s' = { s with mnG := upd s.mnG t (s.mnG t + 1),
                    gcopy := upd s.gcopy t (some { g with active := false }),
                    toL1 := some ⟨t, g.mr, g.exec, s.mnG t + 1, s.slOpen t⟩ } := by
  simp only [valStep] at h
  split at h
  · rename_i g hg
    split_ifs at h with hc
    exact ⟨g, hg, hc.1, hc.2.1, hc.2.2, (Option.some.inj h).symm⟩
  · simp at h

lemma step_mintL1 {K : ValEnv} {W : ValWorld} {s s' : ValState}
    (h : valStep K W s .mintL1 = some s') :
    ∃ r, s.toL1 = some r ∧ W.enabled = true ∧ s.mn = numToSL ∧ r.num = numToL1 ∧
      (s.ivs numToSL).active = true ∧ s.awayL1 = true ∧ s.mrL1 W.c ≤ r.batchNumber ∧
      (K.finalizedAfterExec = true → r.slBatch ≤ s.mrL1 r.src) ∧
      s' = { s with
          mn := r.num
          ivs := upd s.ivs numToSL
            { (s.ivs numToSL) with
              fromGW := r.batchNumber
              upper := s.mrL1 (s.ivs numToSL).sl
              active := false }
          mrL1 := upd s.mrL1 W.c r.batchNumber
          execL1 := r.exec
          awayL1 := false
          toL1 := none } := by
  simp only [valStep] at h
  split at h
  · rename_i r hr
    split_ifs at h with hc
    exact ⟨r, hr, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.1,
      hc.2.2.2.2.2.2, (Option.some.inj h).symm⟩
  · simp at h

/-! ## The invariant -/

/-- No diamond of `c` on a settlement layer settles there. -/
def SLVNoActive (s : ValState) : Prop := ∀ t g, s.gcopy t = some g → g.active = false

/-- Every executed batch of `c` was executed on L1. -/
def SLVAllOnL1 (W : ValWorld) (s : ValState) : Prop :=
  ∀ b r, s.hist b = some r → r.layer = W.l1

/-- What every reachable state has, whatever its phase. -/
structure SLVCommon (K : ValEnv) (W : ValWorld) (s : ValState) : Prop where
  ivs2 : (s.ivs 2).sl = 0
  sealed : K.sealedOnly = true → ∀ t, t ≠ W.c → t ≠ W.l1 → s.mrL1 t < s.slOpen t
  contig : ∀ b, (s.hist b).isSome = true ↔ 1 ≤ b ∧ b ≤ s.total
  execEq : s.execL1 = s.mrL1 W.c

/-- Phase A: `c` settles on L1, `migrationNumber` 0, every executed batch on L1. -/
structure SLVHome (W : ValWorld) (s : ValState) : Prop where
  mn : s.mn = 0
  home : s.awayL1 = false
  noToSL : s.toSL = none
  noToL1 : s.toL1 = none
  noActive : SLVNoActive s
  mrc : s.mrL1 W.c = s.total
  allL1 : SLVAllOnL1 W s

/-- Phase B: burned on L1 towards `t`; the transaction is not minted (it may have failed). -/
structure SLVPending (W : ValWorld) (s : ValState) (t : ℕ) : Prop where
  wl : W.wl t = true
  ne_l1 : t ≠ W.l1
  ne_c : t ≠ W.c
  mn : s.mn = 1
  ivTo : (s.ivs 1).toGW = s.total
  ivSl : (s.ivs 1).sl = t
  ivActive : (s.ivs 1).active = true
  away : s.awayL1 = true
  toSL : ∃ m, s.toSL = some m ∧ m.sl = t ∧ m.batchNumber = s.total ∧ m.exec = s.total ∧
    m.num = 1
  noToL1 : s.toL1 = none
  noActive : SLVNoActive s
  mrc : s.mrL1 W.c = s.total
  allL1 : SLVAllOnL1 W s
  lower : (s.ivs 1).lower ≤ s.mrL1 t

/-- Phase C: `c` settles on `t`. -/
structure SLVOnSL (K : ValEnv) (W : ValWorld) (s : ValState) (t : ℕ) : Prop where
  wl : W.wl t = true
  ne_l1 : t ≠ W.l1
  ne_c : t ≠ W.c
  mn : s.mn = 1
  ivTo : (s.ivs 1).toGW = s.mrL1 W.c
  ivSl : (s.ivs 1).sl = t
  ivActive : (s.ivs 1).active = true
  away : s.awayL1 = true
  noToSL : s.toSL = none
  noToL1 : s.toL1 = none
  copy : s.gcopy t = some ⟨s.total, s.total, true⟩
  others : ∀ t' g, t' ≠ t → s.gcopy t' = some g → g.active = false
  le : s.mrL1 W.c ≤ s.total
  lower : (s.ivs 1).lower ≤ s.mrL1 t
  histL1 : ∀ b r, s.hist b = some r → b ≤ s.mrL1 W.c → r.layer = W.l1
  histSL : ∀ b r, s.hist b = some r → s.mrL1 W.c < b →
    r.layer = t ∧ (K.sealedOnly = true → (s.ivs 1).lower < r.slBatch) ∧ r.slBatch ≤ s.slOpen t

/-- Phase D: burned on `t` back to L1 with message `m`, not yet minted on L1. -/
structure SLVReturning (K : ValEnv) (W : ValWorld) (s : ValState) (t : ℕ) (m : ToL1Msg) :
    Prop where
  wl : W.wl t = true
  ne_l1 : t ≠ W.l1
  ne_c : t ≠ W.c
  mn : s.mn = 1
  ivTo : (s.ivs 1).toGW = s.mrL1 W.c
  ivSl : (s.ivs 1).sl = t
  ivActive : (s.ivs 1).active = true
  away : s.awayL1 = true
  noToSL : s.toSL = none
  toL1 : s.toL1 = some m
  src : m.src = t
  bn : m.batchNumber = s.total
  ex : m.exec = s.total
  noActive : SLVNoActive s
  le : s.mrL1 W.c ≤ s.total
  histL1 : ∀ b r, s.hist b = some r → b ≤ s.mrL1 W.c → r.layer = W.l1
  histSL : ∀ b r, s.hist b = some r → s.mrL1 W.c < b →
    r.layer = t ∧ (K.sealedOnly = true → (s.ivs 1).lower < r.slBatch) ∧ r.slBatch ≤ m.slBatch

/-- Phase E: back on L1 after the round trip through `t`; interval 1 is closed. -/
structure SLVBack (K : ValEnv) (W : ValWorld) (s : ValState) (t : ℕ) : Prop where
  wl : W.wl t = true
  ne_l1 : t ≠ W.l1
  ne_c : t ≠ W.c
  mn : s.mn = 2
  ivSl : (s.ivs 1).sl = t
  ivActive : (s.ivs 1).active = false
  home : s.awayL1 = false
  noToSL : s.toSL = none
  noToL1 : s.toL1 = none
  noActive : SLVNoActive s
  mrc : s.mrL1 W.c = s.total
  fromLe : (s.ivs 1).fromGW ≤ s.total
  histL1 : ∀ b r, s.hist b = some r → (b ≤ (s.ivs 1).toGW ∨ (s.ivs 1).fromGW < b) →
    r.layer = W.l1
  histSL : ∀ b r, s.hist b = some r → (s.ivs 1).toGW < b → b ≤ (s.ivs 1).fromGW →
    r.layer = t ∧ (K.sealedOnly = true → (s.ivs 1).lower < r.slBatch) ∧
    (K.finalizedAfterExec = true → r.slBatch ≤ (s.ivs 1).upper)

/-- The reachable-state invariant: the common part and one phase. -/
inductive SLVInv (K : ValEnv) (W : ValWorld) (s : ValState) : Prop
  | home : SLVCommon K W s → SLVHome W s → SLVInv K W s
  | pending (t : ℕ) : SLVCommon K W s → SLVPending W s t → SLVInv K W s
  | onSL (t : ℕ) : SLVCommon K W s → SLVOnSL K W s t → SLVInv K W s
  | returning (t : ℕ) (m : ToL1Msg) : SLVCommon K W s → SLVReturning K W s t m → SLVInv K W s
  | back (t : ℕ) : SLVCommon K W s → SLVBack K W s t → SLVInv K W s

lemma SLVInv.common {K : ValEnv} {W : ValWorld} {s : ValState} (hI : SLVInv K W s) :
    SLVCommon K W s := by
  cases hI <;> assumption

/-! ## Preservation, one label at a time -/

theorem slvInv_execL1 {K : ValEnv} {W : ValWorld} {s s' : ValState} {b : ℕ}
    (hI : SLVInv K W s) (h : valStep K W s (.execL1 b) = some s') : SLVInv K W s' := by
  obtain ⟨hhome, hb1, hb2, rfl⟩ := step_execL1 h
  have hC := hI.common
  -- the common part, given that L1's counter of `c` is `total`
  have common : s.mrL1 W.c = s.total → b = s.total + 1 →
      SLVCommon K W { s with
        mrL1 := upd s.mrL1 W.c b, execL1 := b,
        hist := upd s.hist b (some ⟨W.l1, 0⟩), total := s.total + 1 } := by
    intro _ hb
    subst hb
    refine ⟨hC.ivs2, ?_, contig_push hC.contig _, ?_⟩
    · intro hs t ht1 ht2
      show upd s.mrL1 W.c (s.total + 1) t < s.slOpen t
      rw [upd_ne _ _ ht1]
      exact hC.sealed hs t ht1 ht2
    · show s.total + 1 = upd s.mrL1 W.c (s.total + 1) W.c
      simp
  cases hI with
  | home _ hA =>
    have hb : b = s.total + 1 := by rw [hb1, hA.mrc]
    refine .home (common hA.mrc hb) ?_
    subst hb
    refine ⟨hA.mn, hhome, hA.noToSL, hA.noToL1, hA.noActive, by simp, ?_⟩
    intro x r hx
    rcases upd_some_cases hx with ⟨_, rfl⟩ | ⟨_, hx'⟩
    · rfl
    · exact hA.allL1 x r hx'
  | pending _ _ hB => simp [hB.away] at hhome
  | onSL _ _ hO => simp [hO.away] at hhome
  | returning _ _ _ hD => simp [hD.away] at hhome
  | back t _ hE =>
    have hb : b = s.total + 1 := by rw [hb1, hE.mrc]
    refine .back t (common hE.mrc hb) ?_
    subst hb
    have hfl := hE.fromLe
    refine ⟨hE.wl, hE.ne_l1, hE.ne_c, hE.mn, hE.ivSl, hE.ivActive, hhome, hE.noToSL, hE.noToL1,
      hE.noActive, by simp, by show (s.ivs 1).fromGW ≤ s.total + 1; omega, ?_, ?_⟩
    · intro x r hx hxr
      rcases upd_some_cases hx with ⟨_, rfl⟩ | ⟨_, hx'⟩
      · rfl
      · exact hE.histL1 x r hx' hxr
    · intro x r hx h1 h2
      rcases upd_some_cases hx with ⟨rfl, rfl⟩ | ⟨_, hx'⟩
      · exact absurd h2 (by show ¬ s.total + 1 ≤ (s.ivs 1).fromGW; omega)
      · exact hE.histSL x r hx' h1 h2

theorem slvInv_execSL {K : ValEnv} {W : ValWorld} {s s' : ValState} {t' b : ℕ}
    (hI : SLVInv K W s) (h : valStep K W s (.execSL t' b) = some s') : SLVInv K W s' := by
  obtain ⟨g, hg, hact, hb1, hb2, rfl⟩ := step_execSL h
  cases hI with
  | home _ hA => simp [hA.noActive t' g hg] at hact
  | pending _ _ hB => simp [hB.noActive t' g hg] at hact
  | returning _ _ _ hD => simp [hD.noActive t' g hg] at hact
  | back _ _ hE => simp [hE.noActive t' g hg] at hact
  | onSL t hC hO =>
    have htt : t' = t := by
      by_contra hne
      simp [hO.others t' g hne hg] at hact
    subst htt
    have hgg : g = ⟨s.total, s.total, true⟩ := by
      rw [hO.copy] at hg; exact (Option.some.inj hg).symm
    subst hgg
    have hb : b = s.total + 1 := hb1
    subst hb
    refine .onSL t' ⟨hC.ivs2, hC.sealed, contig_push hC.contig _, hC.execEq⟩ ?_
    have hle := hO.le
    refine ⟨hO.wl, hO.ne_l1, hO.ne_c, hO.mn, hO.ivTo, hO.ivSl, hO.ivActive, hO.away, hO.noToSL,
      hO.noToL1, by simp, ?_, by show s.mrL1 W.c ≤ s.total + 1; omega, hO.lower, ?_, ?_⟩
    · intro t'' g' hne hg'
      dsimp only at hg'
      rw [upd_ne _ _ hne] at hg'
      exact hO.others t'' g' hne hg'
    · intro x r hx hxr
      rcases upd_some_cases hx with ⟨rfl, rfl⟩ | ⟨_, hx'⟩
      · exact absurd hxr (by show ¬ s.total + 1 ≤ s.mrL1 W.c; omega)
      · exact hO.histL1 x r hx' hxr
    · intro x r hx hxr
      rcases upd_some_cases hx with ⟨rfl, rfl⟩ | ⟨_, hx'⟩
      · refine ⟨rfl, fun hs => ?_, le_refl _⟩
        exact lt_of_le_of_lt hO.lower (hC.sealed hs t' hO.ne_c hO.ne_l1)
      · exact hO.histSL x r hx' hxr

theorem slvInv_slSeal {K : ValEnv} {W : ValWorld} {s s' : ValState} {t' : ℕ}
    (hI : SLVInv K W s) (h : valStep K W s (.slSeal t') = some s') : SLVInv K W s' := by
  obtain rfl := step_slSeal h
  have hmono : ∀ x, s.slOpen x ≤ upd s.slOpen t' (s.slOpen t' + 1) x := upd_succ_ge s.slOpen t'
  have common : SLVCommon K W s → SLVCommon K W { s with slOpen := upd s.slOpen t' (s.slOpen t' + 1) } :=
    fun hC => ⟨hC.ivs2, fun hs t ht1 ht2 => lt_of_lt_of_le (hC.sealed hs t ht1 ht2) (hmono t),
      hC.contig, hC.execEq⟩
  cases hI with
  | home hC hA =>
    exact .home (common hC) ⟨hA.mn, hA.home, hA.noToSL, hA.noToL1, hA.noActive, hA.mrc, hA.allL1⟩
  | pending t hC hB =>
    exact .pending t (common hC) ⟨hB.wl, hB.ne_l1, hB.ne_c, hB.mn, hB.ivTo, hB.ivSl, hB.ivActive,
      hB.away, hB.toSL, hB.noToL1, hB.noActive, hB.mrc, hB.allL1, hB.lower⟩
  | returning t m hC hD =>
    exact .returning t m (common hC) ⟨hD.wl, hD.ne_l1, hD.ne_c, hD.mn, hD.ivTo, hD.ivSl,
      hD.ivActive, hD.away, hD.noToSL, hD.toL1, hD.src, hD.bn, hD.ex, hD.noActive, hD.le,
      hD.histL1, hD.histSL⟩
  | back t hC hE =>
    exact .back t (common hC) ⟨hE.wl, hE.ne_l1, hE.ne_c, hE.mn, hE.ivSl, hE.ivActive, hE.home,
      hE.noToSL, hE.noToL1, hE.noActive, hE.mrc, hE.fromLe, hE.histL1, hE.histSL⟩
  | onSL t hC hO =>
    refine .onSL t (common hC) ⟨hO.wl, hO.ne_l1, hO.ne_c, hO.mn, hO.ivTo, hO.ivSl, hO.ivActive,
      hO.away, hO.noToSL, hO.noToL1, hO.copy, hO.others, hO.le, hO.lower, hO.histL1, ?_⟩
    intro x r hx hxr
    obtain ⟨h1, h2, h3⟩ := hO.histSL x r hx hxr
    exact ⟨h1, h2, le_trans h3 (hmono t)⟩

theorem slvInv_slExecL1 {K : ValEnv} {W : ValWorld} {s s' : ValState} {t' : ℕ}
    (hI : SLVInv K W s) (h : valStep K W s (.slExecL1 t') = some s') : SLVInv K W s' := by
  obtain ⟨hc, hl1, hseal, rfl⟩ := step_slExecL1 h
  have hcc : upd s.mrL1 t' (s.mrL1 t' + 1) W.c = s.mrL1 W.c := upd_ne _ _ (Ne.symm hc)
  have hmono : ∀ x, s.mrL1 x ≤ upd s.mrL1 t' (s.mrL1 t' + 1) x := upd_succ_ge s.mrL1 t'
  have common : SLVCommon K W s →
      SLVCommon K W { s with mrL1 := upd s.mrL1 t' (s.mrL1 t' + 1) } := by
    intro hC
    refine ⟨hC.ivs2, ?_, hC.contig, ?_⟩
    · intro hs t ht1 ht2
      show upd s.mrL1 t' (s.mrL1 t' + 1) t < s.slOpen t
      by_cases htt : t = t'
      · subst htt; simp only [upd_self]; exact hseal hs
      · rw [upd_ne _ _ htt]; exact hC.sealed hs t ht1 ht2
    · show s.execL1 = upd s.mrL1 t' (s.mrL1 t' + 1) W.c
      rw [hcc]; exact hC.execEq
  cases hI with
  | home hC hA =>
    exact .home (common hC) ⟨hA.mn, hA.home, hA.noToSL, hA.noToL1, hA.noActive,
      by show upd s.mrL1 t' (s.mrL1 t' + 1) W.c = s.total; rw [hcc]; exact hA.mrc, hA.allL1⟩
  | pending t hC hB =>
    exact .pending t (common hC) ⟨hB.wl, hB.ne_l1, hB.ne_c, hB.mn, hB.ivTo, hB.ivSl, hB.ivActive,
      hB.away, hB.toSL, hB.noToL1, hB.noActive,
      by show upd s.mrL1 t' (s.mrL1 t' + 1) W.c = s.total; rw [hcc]; exact hB.mrc, hB.allL1,
      le_trans hB.lower (hmono t)⟩
  | onSL t hC hO =>
    refine .onSL t (common hC) ⟨hO.wl, hO.ne_l1, hO.ne_c, hO.mn, ?_, hO.ivSl, hO.ivActive,
      hO.away, hO.noToSL, hO.noToL1, hO.copy, hO.others, ?_, le_trans hO.lower (hmono t), ?_, ?_⟩
    · show (s.ivs 1).toGW = upd s.mrL1 t' (s.mrL1 t' + 1) W.c
      rw [hcc]; exact hO.ivTo
    · show upd s.mrL1 t' (s.mrL1 t' + 1) W.c ≤ s.total
      rw [hcc]; exact hO.le
    · intro x r hx hxr
      exact hO.histL1 x r hx (by rw [← hcc]; exact hxr)
    · intro x r hx hxr
      exact hO.histSL x r hx (by rw [← hcc]; exact hxr)
  | returning t m hC hD =>
    refine .returning t m (common hC) ⟨hD.wl, hD.ne_l1, hD.ne_c, hD.mn, ?_, hD.ivSl, hD.ivActive,
      hD.away, hD.noToSL, hD.toL1, hD.src, hD.bn, hD.ex, hD.noActive, ?_, ?_, ?_⟩
    · show (s.ivs 1).toGW = upd s.mrL1 t' (s.mrL1 t' + 1) W.c
      rw [hcc]; exact hD.ivTo
    · show upd s.mrL1 t' (s.mrL1 t' + 1) W.c ≤ s.total
      rw [hcc]; exact hD.le
    · intro x r hx hxr
      exact hD.histL1 x r hx (by rw [← hcc]; exact hxr)
    · intro x r hx hxr
      exact hD.histSL x r hx (by rw [← hcc]; exact hxr)
  | back t hC hE =>
    exact .back t (common hC) ⟨hE.wl, hE.ne_l1, hE.ne_c, hE.mn, hE.ivSl, hE.ivActive, hE.home,
      hE.noToSL, hE.noToL1, hE.noActive,
      by show upd s.mrL1 t' (s.mrL1 t' + 1) W.c = s.total; rw [hcc]; exact hE.mrc, hE.fromLe,
      hE.histL1, hE.histSL⟩

theorem slvInv_burnL1 {K : ValEnv} {W : ValWorld} {s s' : ValState} {t : ℕ}
    (hI : SLVInv K W s) (h : valStep K W s (.burnL1 t) = some s') : SLVInv K W s' := by
  obtain ⟨_, hwl, hhome, hwlc, _, hl1, hnum, rfl⟩ := step_burnL1 h
  have hmn : s.mn = 0 := by simpa [numToSL] using hnum
  cases hI with
  | pending _ _ hB => simp [hB.away] at hhome
  | onSL _ _ hO => simp [hO.away] at hhome
  | returning _ _ _ hD => simp [hD.away] at hhome
  | back _ _ hE => simp [hE.mn] at hmn
  | home hC hA =>
    have htc : t ≠ W.c := by
      intro htc; subst htc; simp [hwl] at hwlc
    rw [hmn]
    refine .pending t ⟨?_, hC.sealed, hC.contig, hC.execEq⟩ ?_
    · show (upd s.ivs (0 + 1) ⟨s.mrL1 W.c, 0, s.mrL1 t, 0, t, true⟩ 2).sl = 0
      rw [upd_ne _ _ (by decide)]; exact hC.ivs2
    · refine ⟨hwl, hl1, htc, rfl, ?_, ?_, ?_, rfl, ?_, hA.noToL1, hA.noActive, hA.mrc, hA.allL1, ?_⟩
      · show (upd s.ivs (0 + 1) ⟨s.mrL1 W.c, 0, s.mrL1 t, 0, t, true⟩ 1).toGW = s.total
        simp [hA.mrc]
      · show (upd s.ivs (0 + 1) ⟨s.mrL1 W.c, 0, s.mrL1 t, 0, t, true⟩ 1).sl = t
        simp
      · show (upd s.ivs (0 + 1) ⟨s.mrL1 W.c, 0, s.mrL1 t, 0, t, true⟩ 1).active = true
        simp
      · exact ⟨_, rfl, rfl, hA.mrc, hC.execEq.trans hA.mrc, rfl⟩
      · show (upd s.ivs (0 + 1) ⟨s.mrL1 W.c, 0, s.mrL1 t, 0, t, true⟩ 1).lower ≤ s.mrL1 t
        simp

theorem slvInv_mintSL {K : ValEnv} {W : ValWorld} {s s' : ValState}
    (hI : SLVInv K W s) (h : valStep K W s .mintSL = some s') : SLVInv K W s' := by
  obtain ⟨m, hm, _, _, _, rfl⟩ := step_mintSL h
  cases hI with
  | home _ hA => simp [hA.noToSL] at hm
  | onSL _ _ hO => simp [hO.noToSL] at hm
  | returning _ _ _ hD => simp [hD.noToSL] at hm
  | back _ _ hE => simp [hE.noToSL] at hm
  | pending t hC hB =>
    obtain ⟨m', hm', hsl, hbn, hex, _⟩ := hB.toSL
    rw [hm] at hm'
    obtain rfl := Option.some.inj hm'
    subst hsl
    refine .onSL m.sl ⟨hC.ivs2, hC.sealed, hC.contig, hC.execEq⟩ ?_
    refine ⟨hB.wl, hB.ne_l1, hB.ne_c, hB.mn, hB.ivTo.trans hB.mrc.symm, hB.ivSl, hB.ivActive,
      hB.away, rfl, hB.noToL1, ?_, ?_, le_of_eq hB.mrc, hB.lower, ?_, ?_⟩
    · show upd s.gcopy m.sl (some ⟨m.exec, m.batchNumber, true⟩) m.sl = some ⟨s.total, s.total, true⟩
      rw [upd_self, hbn, hex]
    · intro t' g hne hg
      dsimp only at hg
      rw [upd_ne _ _ hne] at hg
      exact hB.noActive t' g hg
    · intro x r hx _
      exact hB.allL1 x r hx
    · intro x r hx hxr
      have := hist_le_total hC.contig hx
      exact absurd hxr (by show ¬ s.mrL1 W.c < x; rw [hB.mrc]; omega)

theorem slvInv_failSL {K : ValEnv} {W : ValWorld} {s s' : ValState}
    (hI : SLVInv K W s) (h : valStep K W s .failSL = some s') : SLVInv K W s' := by
  obtain ⟨m, hm, _, rfl⟩ := step_failSL h
  cases hI with
  | home _ hA => simp [hA.noToSL] at hm
  | onSL _ _ hO => simp [hO.noToSL] at hm
  | returning _ _ _ hD => simp [hD.noToSL] at hm
  | back _ _ hE => simp [hE.noToSL] at hm
  | pending t hC hB =>
    obtain ⟨m', hm', hsl, hbn, hex, hnum⟩ := hB.toSL
    rw [hm] at hm'
    obtain rfl := Option.some.inj hm'
    exact .pending t ⟨hC.ivs2, hC.sealed, hC.contig, hC.execEq⟩ ⟨hB.wl, hB.ne_l1, hB.ne_c, hB.mn,
      hB.ivTo, hB.ivSl, hB.ivActive, hB.away, ⟨_, rfl, hsl, hbn, hex, hnum⟩, hB.noToL1,
      hB.noActive, hB.mrc, hB.allL1, hB.lower⟩

theorem slvInv_confirmFailure {K : ValEnv} {W : ValWorld} {s s' : ValState}
    (hI : SLVInv K W s) (h : valStep K W s .confirmFailure = some s') : SLVInv K W s' := by
  obtain ⟨m, hm, _, hmn, _, rfl⟩ := step_confirmFailure h
  cases hI with
  | home _ hA => simp [hA.noToSL] at hm
  | onSL _ _ hO => simp [hO.noToSL] at hm
  | returning _ _ _ hD => simp [hD.noToSL] at hm
  | back _ _ hE => simp [hE.mn, numToSL] at hmn
  | pending t hC hB =>
    rw [hB.mn]
    refine .home ⟨?_, hC.sealed, hC.contig, hC.execEq⟩
      ⟨rfl, rfl, rfl, hB.noToL1, hB.noActive, hB.mrc, hB.allL1⟩
    show (upd s.ivs 1 MigInterval.empty 2).sl = 0
    rw [upd_ne _ _ (by decide)]; exact hC.ivs2

theorem slvInv_burnSL {K : ValEnv} {W : ValWorld} {s s' : ValState} {t' : ℕ}
    (hI : SLVInv K W s) (h : valStep K W s (.burnSL t') = some s') : SLVInv K W s' := by
  obtain ⟨g, hg, _, hact, _, rfl⟩ := step_burnSL h
  cases hI with
  | home _ hA => simp [hA.noActive t' g hg] at hact
  | pending _ _ hB => simp [hB.noActive t' g hg] at hact
  | returning _ _ _ hD => simp [hD.noActive t' g hg] at hact
  | back _ _ hE => simp [hE.noActive t' g hg] at hact
  | onSL t hC hO =>
    have htt : t' = t := by
      by_contra hne
      simp [hO.others t' g hne hg] at hact
    subst htt
    have hgg : g = ⟨s.total, s.total, true⟩ := by
      rw [hO.copy] at hg; exact (Option.some.inj hg).symm
    subst hgg
    refine .returning t' _ ⟨hC.ivs2, hC.sealed, hC.contig, hC.execEq⟩
      ⟨hO.wl, hO.ne_l1, hO.ne_c, hO.mn, hO.ivTo, hO.ivSl, hO.ivActive, hO.away, hO.noToSL, rfl,
        rfl, rfl, rfl, ?_, hO.le, hO.histL1, hO.histSL⟩
    intro t'' g' hg'
    dsimp only at hg'
    by_cases hne : t'' = t'
    · subst hne
      simp only [upd_self, Option.some.injEq] at hg'
      rw [← hg']
    · rw [upd_ne _ _ hne] at hg'
      exact hO.others t'' g' hne hg'

theorem slvInv_mintL1 {K : ValEnv} {W : ValWorld} {s s' : ValState}
    (hI : SLVInv K W s) (h : valStep K W s .mintL1 = some s') : SLVInv K W s' := by
  obtain ⟨r, hr, _, _, hnum, _, _, _, hfin, rfl⟩ := step_mintL1 h
  cases hI with
  | home _ hA => simp [hA.noToL1] at hr
  | pending _ _ hB => simp [hB.noToL1] at hr
  | onSL _ _ hO => simp [hO.noToL1] at hr
  | back _ _ hE => simp [hE.noToL1] at hr
  | returning t m hC hD =>
    rw [hD.toL1] at hr
    obtain rfl := Option.some.inj hr
    have hnum2 : m.num = 2 := hnum
    refine .back t ⟨?_, ?_, hC.contig, ?_⟩ ⟨hD.wl, hD.ne_l1, hD.ne_c, hnum2, ?_, ?_, rfl,
      hD.noToSL, rfl, hD.noActive, ?_, ?_, ?_, ?_⟩
    · dsimp only
      rw [upd_ne _ _ (by decide)]; exact hC.ivs2
    · intro hs t' ht1 ht2
      dsimp only
      rw [upd_ne _ _ ht1]; exact hC.sealed hs t' ht1 ht2
    · dsimp only
      rw [upd_self, hD.ex, hD.bn]
    · dsimp only
      simp [numToSL, hD.ivSl]
    · dsimp only
      simp [numToSL]
    · dsimp only
      rw [upd_self, hD.bn]
    · dsimp only
      simp [numToSL, hD.bn]
    · intro x r hx hxr
      dsimp only at hx hxr
      simp only [numToSL, upd_self] at hxr
      rw [hD.ivTo, hD.bn] at hxr
      have := hist_le_total hC.contig hx
      rcases hxr with hxr | hxr
      · exact hD.histL1 x r hx hxr
      · omega
    · intro x r hx h1 _
      dsimp only at hx h1 ⊢
      simp only [numToSL, upd_self] at h1 ⊢
      rw [hD.ivTo] at h1
      obtain ⟨hl, hs, hk⟩ := hD.histSL x r hx h1
      refine ⟨hl, hs, fun hf => ?_⟩
      have := hfin hf
      rw [hD.src] at this
      rw [hD.ivSl]
      exact le_trans hk this

/-! ## Preservation and the start -/

/-- Every successful step keeps the invariant, in every environment and world. -/
theorem slvInv_step {K : ValEnv} {W : ValWorld} {s s' : ValState} {l : ValLabel}
    (hI : SLVInv K W s) (h : valStep K W s l = some s') : SLVInv K W s' := by
  cases l with
  | execL1 b => exact slvInv_execL1 hI h
  | execSL t b => exact slvInv_execSL hI h
  | slSeal t => exact slvInv_slSeal hI h
  | slExecL1 t => exact slvInv_slExecL1 hI h
  | burnL1 t => exact slvInv_burnL1 hI h
  | mintSL => exact slvInv_mintSL hI h
  | failSL => exact slvInv_failSL hI h
  | confirmFailure => exact slvInv_confirmFailure hI h
  | burnSL t => exact slvInv_burnSL hI h
  | mintL1 => exact slvInv_mintL1 hI h

/-- A run keeps the invariant. -/
theorem slvInv_run {K : ValEnv} {W : ValWorld} :
    ∀ {s s' : ValState} {ls : List ValLabel}, SLVInv K W s → valRun K W s ls = some s' →
      SLVInv K W s'
  | s, s', [], hI, h => by
    simp only [valRun, Option.some.injEq] at h
    exact h ▸ hI
  | s, s', l :: ls, hI, h => by
    simp only [valRun] at h
    cases hs : valStep K W s l with
    | none => rw [hs] at h; simp at h
    | some s1 =>
      rw [hs] at h
      exact slvInv_run (slvInv_step hI hs) h

/-- A start state satisfies the invariant. -/
theorem slvInv_init {K : ValEnv} {W : ValWorld} {s : ValState} (h : ValInit W s) :
    SLVInv K W s := by
  obtain ⟨hmn, h2, hhome, htoSL, htoL1, hex, hmrc, hcopy, hopen, hcontig, hl1⟩ := h
  exact .home ⟨h2, fun _ t ht1 ht2 => hopen t ht1 ht2, hcontig, hex.trans hmrc.symm⟩
    ⟨hmn, hhome, htoSL, htoL1, hcopy, hmrc, hl1⟩

/-! ## Steps never rewrite a recorded batch -/

/-- A successful step from a state satisfying the invariant keeps every recorded batch. -/
theorem slv_hist_step {K : ValEnv} {W : ValWorld} {s s' : ValState} {l : ValLabel}
    (hI : SLVInv K W s) (h : valStep K W s l = some s') :
    ∀ b r, s.hist b = some r → s'.hist b = some r := by
  have hC := hI.common
  intro x r hx
  have hxle := hist_le_total hC.contig hx
  cases l with
  | execL1 b =>
    obtain ⟨hhome, hb1, _, rfl⟩ := step_execL1 h
    have hmrc : s.mrL1 W.c = s.total := by
      cases hI with
      | home _ hA => exact hA.mrc
      | pending _ _ hB => simp [hB.away] at hhome
      | onSL _ _ hO => simp [hO.away] at hhome
      | returning _ _ _ hD => simp [hD.away] at hhome
      | back _ _ hE => exact hE.mrc
    show upd s.hist b _ x = some r
    rw [upd_ne _ _ (by omega)]; exact hx
  | execSL t b =>
    obtain ⟨g, hg, hact, hb1, _, rfl⟩ := step_execSL h
    have hmr : g.mr = s.total := by
      cases hI with
      | home _ hA => simp [hA.noActive t g hg] at hact
      | pending _ _ hB => simp [hB.noActive t g hg] at hact
      | returning _ _ _ hD => simp [hD.noActive t g hg] at hact
      | back _ _ hE => simp [hE.noActive t g hg] at hact
      | onSL t0 _ hO =>
        by_cases hne : t = t0
        · subst hne; rw [hO.copy] at hg; rw [← Option.some.inj hg]
        · simp [hO.others t g hne hg] at hact
    show upd s.hist b _ x = some r
    rw [upd_ne _ _ (by omega)]; exact hx
  | slSeal t => obtain rfl := step_slSeal h; exact hx
  | slExecL1 t => obtain ⟨_, _, _, rfl⟩ := step_slExecL1 h; exact hx
  | burnL1 t => obtain ⟨_, _, _, _, _, _, _, rfl⟩ := step_burnL1 h; exact hx
  | mintSL => obtain ⟨_, _, _, _, _, rfl⟩ := step_mintSL h; exact hx
  | failSL => obtain ⟨_, _, _, rfl⟩ := step_failSL h; exact hx
  | confirmFailure => obtain ⟨_, _, _, _, _, rfl⟩ := step_confirmFailure h; exact hx
  | burnSL t => obtain ⟨_, _, _, _, _, rfl⟩ := step_burnSL h; exact hx
  | mintL1 => obtain ⟨_, _, _, _, _, _, _, _, _, rfl⟩ := step_mintL1 h; exact hx

/-- A run from a state satisfying the invariant keeps every recorded batch. -/
theorem slv_hist_run {K : ValEnv} {W : ValWorld} :
    ∀ {s s' : ValState} {ls : List ValLabel}, SLVInv K W s → valRun K W s ls = some s' →
      ∀ b r, s.hist b = some r → s'.hist b = some r
  | s, s', [], _, h => by
    simp only [valRun, Option.some.injEq] at h
    exact fun b r hb => h ▸ hb
  | s, s', l :: ls, hI, h => by
    simp only [valRun] at h
    cases hs : valStep K W s l with
    | none => rw [hs] at h; simp at h
    | some s1 =>
      rw [hs] at h
      exact fun b r hb => slv_hist_run (slvInv_step hI hs) h b r (slv_hist_step hI hs b r hb)

end Contracts.L1ChainAssetHandler.SettlementLayerValidation
