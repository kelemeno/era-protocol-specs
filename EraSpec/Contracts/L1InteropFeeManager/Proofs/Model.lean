import EraSpec.Contracts.L1InteropFeeManager.Properties.Model

/-!
# Proofs: the interop fee ledger balances, and who can move what

`LedgerBalanced` is an induction on `Reach` with `Balanced` as the invariant; the sum over
all chain ids changes by the change of the one entry written (`total_setBal_same`).
One-step results are case analyses of `Step`.
-/

namespace Contracts.L1InteropFeeManager

private lemma setBal_same (b : UInt256 → Address → ℕ) (c : UInt256) (t : Address) (v : ℕ) :
    setBal b c t v c t = v := by simp [setBal]

private lemma setBal_other {b : UInt256 → Address → ℕ} {c c' : UInt256} {t t' : Address}
    {v : ℕ} (h : ¬ (c' = c ∧ t' = t)) : setBal b c t v c' t' = b c' t' := by
  simp [setBal, h]

private lemma setBal_ne {b : UInt256 → Address → ℕ} {c c' : UInt256} {t t' : Address} {v : ℕ}
    (h : setBal b c t v c' t' ≠ b c' t') : c' = c ∧ t' = t := by
  by_contra hn
  exact h (setBal_other hn)

private lemma bump_same (f : Address → ℕ) (t : Address) (a : ℕ) : bump f t a t = f t + a := by
  simp [bump]

private lemma bump_other {f : Address → ℕ} {t t' : Address} {a : ℕ} (h : t' ≠ t) :
    bump f t a t' = f t' := by
  simp [bump, h]

private lemma bump_ge (f : Address → ℕ) (t t' : Address) (a : ℕ) : f t' ≤ bump f t a t' := by
  unfold bump
  split_ifs <;> omega

private lemma clear_same (f : Address → ℕ) (t : Address) : clear f t t = 0 := by
  simp [clear]

private lemma clear_other {f : Address → ℕ} {t t' : Address} (h : t' ≠ t) :
    clear f t t' = f t' := by
  simp [clear, h]

private lemma clear_ne {f : Address → ℕ} {t t' : Address} (h : clear f t t' ≠ f t') :
    t' = t := by
  by_contra hn
  exact h (clear_other hn)

/-- Writing one entry changes the sum over all chains by that entry's change. -/
private lemma total_setBal_same (b : UInt256 → Address → ℕ) (c : UInt256) (t : Address)
    (v : ℕ) : total (setBal b c t v) t + b c t = total b t + v := by
  have h1 := Finset.add_sum_erase Finset.univ (fun x => setBal b c t v x t) (Finset.mem_univ c)
  have h2 := Finset.add_sum_erase Finset.univ (fun x => b x t) (Finset.mem_univ c)
  have h3 : (Finset.univ.erase c).sum (fun x => setBal b c t v x t) =
      (Finset.univ.erase c).sum (fun x => b x t) :=
    Finset.sum_congr rfl (fun x hx => by
      have hne : x ≠ c := Finset.ne_of_mem_erase hx
      simp [setBal, hne])
  simp only [setBal_same] at h1
  rw [h3] at h1
  unfold total
  omega

private lemma total_setBal_other {b : UInt256 → Address → ℕ} {c : UInt256} {t t' : Address}
    {v : ℕ} (h : t' ≠ t) : total (setBal b c t v) t' = total b t' := by
  unfold total
  exact Finset.sum_congr rfl (fun x _ => by simp [setBal, h])

private lemma balanced_fresh : Balanced fresh :=
  ⟨fun _ _ => rfl, fun _ => rfl, fun t => by simp [fresh, total]⟩

private lemma balanced_step {E : Env} {s s' : State} {l : Label} (hB : Balanced s)
    (hs : Step E s l s') : Balanced s' := by
  cases hs with
  | init _ _ _ _ _ => exact ⟨hB.chain, hB.fees, hB.held⟩
  | setFee _ _ _ _ => exact ⟨hB.chain, hB.fees, hB.held⟩
  | setFeeRecipient _ _ _ => exact ⟨hB.chain, hB.fees, hB.held⟩
  | chargeZero _ _ => exact hB
  | sweepZero _ _ _ => exact hB
  | transferOwnership _ _ => exact ⟨hB.chain, hB.fees, hB.held⟩
  | acceptOwnership _ _ => exact ⟨hB.chain, hB.fees, hB.held⟩
  | renounceOwnership _ _ => exact ⟨hB.chain, hB.fees, hB.held⟩
  | @deposit caller c tok a v _ _ _ _ _ _ _ _ _ =>
    refine ⟨?_, hB.fees, ?_⟩
    · intro c' t'
      have hc := hB.chain c' t'
      by_cases h : c' = c ∧ t' = tok
      · obtain ⟨h1, h2⟩ := h
        rw [h1, h2] at hc ⊢
        show setBal s.dep c tok (s.dep c tok + a) c tok =
          s.wd c tok + s.chg c tok + setBal s.bal c tok (s.bal c tok + a) c tok
        rw [setBal_same, setBal_same]; omega
      · show setBal s.dep c tok (s.dep c tok + a) c' t' =
          s.wd c' t' + s.chg c' t' + setBal s.bal c tok (s.bal c tok + a) c' t'
        rw [setBal_other h, setBal_other h]; exact hc
    · intro t'
      have ht := hB.held t'
      have h1 := total_setBal_same s.bal c tok (s.bal c tok + a)
      by_cases h : t' = tok
      · rw [h] at ht ⊢
        show bump s.inflow tok a tok =
          s.outflow tok + s.accrued tok + total (setBal s.bal c tok (s.bal c tok + a)) tok
        rw [bump_same]; omega
      · show bump s.inflow tok a t' =
          s.outflow t' + s.accrued t' + total (setBal s.bal c tok (s.bal c tok + a)) t'
        rw [bump_other h, total_setBal_other h]; exact ht
  | @withdraw caller c tok dst a _ _ _ _ _ _ hle _ =>
    refine ⟨?_, hB.fees, ?_⟩
    · intro c' t'
      have hc := hB.chain c' t'
      by_cases h : c' = c ∧ t' = tok
      · obtain ⟨h1, h2⟩ := h
        rw [h1, h2] at hc ⊢
        show s.dep c tok =
          setBal s.wd c tok (s.wd c tok + a) c tok + s.chg c tok +
            setBal s.bal c tok (s.bal c tok - a) c tok
        rw [setBal_same, setBal_same]; omega
      · show s.dep c' t' =
          setBal s.wd c tok (s.wd c tok + a) c' t' + s.chg c' t' +
            setBal s.bal c tok (s.bal c tok - a) c' t'
        rw [setBal_other h, setBal_other h]; exact hc
    · intro t'
      have ht := hB.held t'
      have h1 := total_setBal_same s.bal c tok (s.bal c tok - a)
      by_cases h : t' = tok
      · rw [h] at ht ⊢
        show s.inflow tok =
          bump s.outflow tok a tok + s.accrued tok +
            total (setBal s.bal c tok (s.bal c tok - a)) tok
        rw [bump_same]; omega
      · show s.inflow t' =
          bump s.outflow tok a t' + s.accrued t' +
            total (setBal s.bal c tok (s.bal c tok - a)) t'
        rw [bump_other h, total_setBal_other h]; exact ht
  | @charge caller c b u _ _ _ _ _ hle _ =>
    refine ⟨?_, ?_, ?_⟩
    · intro c' t'
      have hc := hB.chain c' t'
      by_cases h : c' = c ∧ t' = s.feeToken
      · obtain ⟨h1, h2⟩ := h
        rw [h1, h2] at hc ⊢
        show s.dep c s.feeToken =
          s.wd c s.feeToken +
            setBal s.chg c s.feeToken (s.chg c s.feeToken + s.feePerUnit * u) c s.feeToken +
            setBal s.bal c s.feeToken (s.bal c s.feeToken - s.feePerUnit * u) c s.feeToken
        rw [setBal_same, setBal_same]; omega
      · show s.dep c' t' =
          s.wd c' t' +
            setBal s.chg c s.feeToken (s.chg c s.feeToken + s.feePerUnit * u) c' t' +
            setBal s.bal c s.feeToken (s.bal c s.feeToken - s.feePerUnit * u) c' t'
        rw [setBal_other h, setBal_other h]; exact hc
    · intro t'
      have hf := hB.fees t'
      by_cases h : t' = s.feeToken
      · rw [h] at hf ⊢
        show bump s.charged s.feeToken (s.feePerUnit * u) s.feeToken =
          s.swept s.feeToken + bump s.accrued s.feeToken (s.feePerUnit * u) s.feeToken
        rw [bump_same, bump_same]; omega
      · show bump s.charged s.feeToken (s.feePerUnit * u) t' =
          s.swept t' + bump s.accrued s.feeToken (s.feePerUnit * u) t'
        rw [bump_other h, bump_other h]; exact hf
    · intro t'
      have ht := hB.held t'
      have h1 := total_setBal_same s.bal c s.feeToken (s.bal c s.feeToken - s.feePerUnit * u)
      by_cases h : t' = s.feeToken
      · rw [h] at ht ⊢
        show s.inflow s.feeToken =
          s.outflow s.feeToken + bump s.accrued s.feeToken (s.feePerUnit * u) s.feeToken +
            total (setBal s.bal c s.feeToken (s.bal c s.feeToken - s.feePerUnit * u)) s.feeToken
        rw [bump_same]; omega
      · show s.inflow t' =
          s.outflow t' + bump s.accrued s.feeToken (s.feePerUnit * u) t' +
            total (setBal s.bal c s.feeToken (s.bal c s.feeToken - s.feePerUnit * u)) t'
        rw [bump_other h, total_setBal_other h]; exact ht
  | @sweep caller tok _ _ _ _ =>
    refine ⟨hB.chain, ?_, ?_⟩
    · intro t'
      have hf := hB.fees t'
      by_cases h : t' = tok
      · rw [h] at hf ⊢
        show s.charged tok = bump s.swept tok (s.accrued tok) tok + clear s.accrued tok tok
        rw [bump_same, clear_same]; omega
      · show s.charged t' = bump s.swept tok (s.accrued tok) t' + clear s.accrued tok t'
        rw [bump_other h, clear_other h]; exact hf
    · intro t'
      have ht := hB.held t'
      by_cases h : t' = tok
      · rw [h] at ht ⊢
        show s.inflow tok =
          bump s.outflow tok (s.accrued tok) tok + clear s.accrued tok tok + total s.bal tok
        rw [bump_same, clear_same]; omega
      · show s.inflow t' =
          bump s.outflow tok (s.accrued tok) t' + clear s.accrued tok t' + total s.bal t'
        rw [bump_other h, clear_other h]; exact ht

theorem LedgerBalanced : Properties.LedgerBalanced := by
  refine ⟨balanced_fresh, ?_⟩
  intro s₀ s h0 hR
  induction hR with
  | refl => exact h0
  | step _ hs ih => exact balanced_step ih hs

theorem DebitAuthority : Properties.DebitAuthority := by
  intro E s s' l c t hs hlt
  cases hs with
  | init _ _ _ _ _ => exact absurd hlt (lt_irrefl _)
  | setFee _ _ _ _ => exact absurd hlt (lt_irrefl _)
  | setFeeRecipient _ _ _ => exact absurd hlt (lt_irrefl _)
  | chargeZero _ _ => exact absurd hlt (lt_irrefl _)
  | sweepZero _ _ _ => exact absurd hlt (lt_irrefl _)
  | sweep _ _ _ _ => exact absurd hlt (lt_irrefl _)
  | transferOwnership _ _ => exact absurd hlt (lt_irrefl _)
  | acceptOwnership _ _ => exact absurd hlt (lt_irrefl _)
  | renounceOwnership _ _ => exact absurd hlt (lt_irrefl _)
  | @deposit caller c' tok a v _ _ _ _ _ _ _ _ _ =>
    exfalso
    have h : setBal s.bal c' tok (s.bal c' tok + a) c t < s.bal c t := hlt
    obtain ⟨h1, h2⟩ := setBal_ne (ne_of_lt h)
    rw [h1, h2, setBal_same] at h
    omega
  | @withdraw caller c' tok dst a _ _ hz hadm hto _ hle hpay =>
    left
    have h : setBal s.bal c' tok (s.bal c' tok - a) c t < s.bal c t := hlt
    obtain ⟨h1, h2⟩ := setBal_ne (ne_of_lt h)
    subst h1 h2
    subst hadm
    refine ⟨dst, a, rfl, hz, hto, ?_, hpay⟩
    show setBal s.bal c t (s.bal c t - a) c t + a = s.bal c t
    rw [setBal_same]; omega
  | @charge caller c' b u _ _ _ hz hcaller hle _ =>
    right
    have h : setBal s.bal c' s.feeToken (s.bal c' s.feeToken - s.feePerUnit * u) c t <
        s.bal c t := hlt
    obtain ⟨h1, h2⟩ := setBal_ne (ne_of_lt h)
    subst h1 h2
    subst hcaller
    refine ⟨b, u, rfl, hz, rfl, ?_, ?_⟩
    · show setBal s.bal c s.feeToken (s.bal c s.feeToken - s.feePerUnit * u) c s.feeToken +
        s.feePerUnit * u = s.bal c s.feeToken
      rw [setBal_same]; omega
    · show bump s.accrued s.feeToken (s.feePerUnit * u) s.feeToken =
        s.accrued s.feeToken + s.feePerUnit * u
      rw [bump_same]

theorem CreditOnlyByDeposit : Properties.CreditOnlyByDeposit := by
  intro E s s' l c t hs hlt
  cases hs with
  | init _ _ _ _ _ => exact absurd hlt (lt_irrefl _)
  | setFee _ _ _ _ => exact absurd hlt (lt_irrefl _)
  | setFeeRecipient _ _ _ => exact absurd hlt (lt_irrefl _)
  | chargeZero _ _ => exact absurd hlt (lt_irrefl _)
  | sweepZero _ _ _ => exact absurd hlt (lt_irrefl _)
  | sweep _ _ _ _ => exact absurd hlt (lt_irrefl _)
  | transferOwnership _ _ => exact absurd hlt (lt_irrefl _)
  | acceptOwnership _ _ => exact absurd hlt (lt_irrefl _)
  | renounceOwnership _ _ => exact absurd hlt (lt_irrefl _)
  | @deposit caller c' tok a v _ _ htok _ _ _ hz _ _ =>
    have h : s.bal c t < setBal s.bal c' tok (s.bal c' tok + a) c t := hlt
    obtain ⟨h1, h2⟩ := setBal_ne (ne_of_gt h)
    subst h1 h2
    refine ⟨caller, a, v, rfl, htok, hz, ?_⟩
    show setBal s.bal c t (s.bal c t + a) c t = s.bal c t + a
    rw [setBal_same]
  | @withdraw caller c' tok dst a _ _ _ _ _ _ _ _ =>
    exfalso
    have h : s.bal c t < setBal s.bal c' tok (s.bal c' tok - a) c t := hlt
    obtain ⟨h1, h2⟩ := setBal_ne (ne_of_gt h)
    rw [h1, h2, setBal_same] at h
    omega
  | @charge caller c' b u _ _ _ _ _ _ _ =>
    exfalso
    have h : s.bal c t <
        setBal s.bal c' s.feeToken (s.bal c' s.feeToken - s.feePerUnit * u) c t := hlt
    obtain ⟨h1, h2⟩ := setBal_ne (ne_of_gt h)
    rw [h1, h2, setBal_same] at h
    omega

theorem AccruedLeavesOnlyBySweep : Properties.AccruedLeavesOnlyBySweep := by
  intro E s s' l t hs hlt
  cases hs with
  | init _ _ _ _ _ => exact absurd hlt (lt_irrefl _)
  | setFee _ _ _ _ => exact absurd hlt (lt_irrefl _)
  | setFeeRecipient _ _ _ => exact absurd hlt (lt_irrefl _)
  | deposit _ _ _ _ _ _ _ _ _ => exact absurd hlt (lt_irrefl _)
  | withdraw _ _ _ _ _ _ _ _ => exact absurd hlt (lt_irrefl _)
  | chargeZero _ _ => exact absurd hlt (lt_irrefl _)
  | sweepZero _ _ _ => exact absurd hlt (lt_irrefl _)
  | transferOwnership _ _ => exact absurd hlt (lt_irrefl _)
  | acceptOwnership _ _ => exact absurd hlt (lt_irrefl _)
  | renounceOwnership _ _ => exact absurd hlt (lt_irrefl _)
  | @charge caller c b u _ _ _ _ _ _ _ =>
    exfalso
    have h : bump s.accrued s.feeToken (s.feePerUnit * u) t < s.accrued t := hlt
    have := bump_ge s.accrued s.feeToken t (s.feePerUnit * u)
    omega
  | @sweep caller tok _ _ _ hpay =>
    have h : clear s.accrued tok t < s.accrued t := hlt
    have h1 := clear_ne (ne_of_lt h)
    subst h1
    refine ⟨⟨caller, rfl⟩, clear_same _ _, hpay, ?_⟩
    show bump s.outflow t (s.accrued t) t = s.outflow t + s.accrued t
    rw [bump_same]

theorem FeeConfigOnlyByOwner : Properties.FeeConfigOnlyByOwner := by
  intro E s s' l hs h
  cases hs with
  | init _ _ _ _ _ => exact Or.inl ⟨_, _, _, rfl⟩
  | setFee _ hc _ _ => subst hc; exact Or.inr (Or.inl ⟨_, _, rfl⟩)
  | setFeeRecipient _ hc _ => subst hc; exact Or.inr (Or.inr ⟨_, rfl⟩)
  | deposit _ _ _ _ _ _ _ _ _ => rcases h with h | h | h <;> exact absurd rfl h
  | withdraw _ _ _ _ _ _ _ _ => rcases h with h | h | h <;> exact absurd rfl h
  | chargeZero _ _ => rcases h with h | h | h <;> exact absurd rfl h
  | charge _ _ _ _ _ _ _ => rcases h with h | h | h <;> exact absurd rfl h
  | sweepZero _ _ _ => rcases h with h | h | h <;> exact absurd rfl h
  | sweep _ _ _ _ => rcases h with h | h | h <;> exact absurd rfl h
  | transferOwnership _ _ => rcases h with h | h | h <;> exact absurd rfl h
  | acceptOwnership _ _ => rcases h with h | h | h <;> exact absurd rfl h
  | renounceOwnership _ _ => rcases h with h | h | h <;> exact absurd rfl h

/-- The invariant behind `ConfigNonzeroOnceInitialized`. -/
private def CfgInv (s : State) : Prop :=
  (s.initialized = true → s.feeToken ≠ 0 ∧ s.feeRecipient ≠ 0 ∧ s.guard = true) ∧
  (s.initialized = false →
    s.owner = 0 ∧ s.pending = 0 ∧ s.feePerUnit = 0 ∧ ∀ t, s.accrued t = 0)

private lemma cfgInv_step {E : Env} {s s' : State} {l : Label} (hI : CfgInv s)
    (hs : Step E s l s') : CfgInv s' := by
  obtain ⟨hT, hF⟩ := hI
  cases hs with
  | init _ _ _ _ hr =>
    exact ⟨fun _ => ⟨(show ETH ≠ 0 by decide), hr, rfl⟩, fun h => Bool.noConfusion h⟩
  | setFee hc0 hc htok _ =>
    refine ⟨fun h => ⟨htok, (hT h).2.1, (hT h).2.2⟩, fun h => ?_⟩
    exact absurd (hc.trans (hF h).1) hc0
  | setFeeRecipient hc0 hc hr =>
    refine ⟨fun h => ⟨(hT h).1, hr, (hT h).2.2⟩, fun h => ?_⟩
    exact absurd (hc.trans (hF h).1) hc0
  | deposit _ _ _ _ _ _ _ _ _ => exact ⟨hT, hF⟩
  | withdraw _ _ _ _ _ _ _ _ => exact ⟨hT, hF⟩
  | chargeZero _ _ => exact ⟨hT, hF⟩
  | charge _ _ hne _ _ _ _ =>
    refine ⟨hT, fun h => ?_⟩
    have h0 := (hF h).2.2.1
    rw [h0, Nat.zero_mul] at hne
    exact absurd rfl hne
  | sweepZero _ _ _ => exact ⟨hT, hF⟩
  | sweep _ _ hne _ =>
    refine ⟨hT, fun h => ?_⟩
    exact absurd ((hF h).2.2.2 _) hne
  | transferOwnership hc0 hc =>
    refine ⟨hT, fun h => ?_⟩
    exact absurd (hc.trans (hF h).1) hc0
  | acceptOwnership hc0 hp =>
    refine ⟨hT, fun h => ?_⟩
    exact absurd (hp.symm.trans (hF h).2.1) hc0
  | renounceOwnership hc0 hc =>
    refine ⟨hT, fun h => ?_⟩
    exact absurd (hc.trans (hF h).1) hc0

private lemma cfgInv_of_reach {s : State} (hR : Reach fresh s) : CfgInv s := by
  induction hR with
  | refl => exact ⟨fun h => Bool.noConfusion h, fun _ => ⟨rfl, rfl, rfl, fun _ => rfl⟩⟩
  | step _ hs ih => exact cfgInv_step ih hs

theorem ConfigNonzeroOnceInitialized : Properties.ConfigNonzeroOnceInitialized :=
  fun _ hR => cfgInv_of_reach hR

theorem SweepNeverPaysZeroAddress : Properties.SweepNeverPaysZeroAddress := by
  intro E s s' caller t hR hs hne
  obtain ⟨hT, hF⟩ := cfgInv_of_reach hR
  cases hs with
  | sweepZero _ _ _ => exact absurd rfl hne
  | sweep _ _ hacc _ =>
    cases hi : s.initialized with
    | true => exact (hT hi).2.1
    | false => exact absurd ((hF hi).2.2.2 _) hacc

/-- `Initializable._initialized` is never cleared. -/
private lemma initialized_mono {s s' : State} (hR : Reach s s') (h : s.initialized = true) :
    s'.initialized = true := by
  induction hR with
  | refl => exact h
  | step _ hs ih =>
    cases hs with
    | init _ _ _ _ _ => rfl
    | setFee _ _ _ _ => exact ih
    | setFeeRecipient _ _ _ => exact ih
    | deposit _ _ _ _ _ _ _ _ _ => exact ih
    | withdraw _ _ _ _ _ _ _ _ => exact ih
    | chargeZero _ _ => exact ih
    | charge _ _ _ _ _ _ _ => exact ih
    | sweepZero _ _ _ => exact ih
    | sweep _ _ _ _ => exact ih
    | transferOwnership _ _ => exact ih
    | acceptOwnership _ _ => exact ih
    | renounceOwnership _ _ => exact ih

theorem InitializeOnce : Properties.InitializeOnce := by
  intro E E' s s' s'' s''' c o r c' o' r' h1 hR h2
  have hi : s'.initialized = true := by
    cases h1 with
    | init _ _ _ _ _ => rfl
  have hi'' := initialized_mono hR hi
  cases h2 with
  | init _ _ hf _ _ => rw [hi''] at hf; exact Bool.noConfusion hf

theorem ZeroFeeChargeOpenToAnyone : Properties.ZeroFeeChargeOpenToAnyone := by
  intro E s caller c b u hc h0
  refine ⟨.chargeZero hc h0, fun s' hs => ?_⟩
  cases hs with
  | chargeZero _ _ => rfl
  | charge _ _ hne _ _ _ _ => exact absurd h0 hne

theorem RenouncedOwnerFreezesConfig : Properties.RenouncedOwnerFreezesConfig := by
  intro s s' hi ho hp hR
  suffices h : s'.initialized = true ∧ s'.owner = 0 ∧ s'.pending = 0 ∧
      s'.feeToken = s.feeToken ∧ s'.feePerUnit = s.feePerUnit ∧
      s'.feeRecipient = s.feeRecipient from h.2
  induction hR with
  | refl => exact ⟨hi, ho, hp, rfl, rfl, rfl⟩
  | step _ hs ih =>
    obtain ⟨i1, i2, i3, i4, i5, i6⟩ := ih
    cases hs with
    | init _ _ hf _ _ => rw [i1] at hf; exact Bool.noConfusion hf
    | setFee hc0 hc _ _ => exact absurd (hc.trans i2) hc0
    | setFeeRecipient hc0 hc _ => exact absurd (hc.trans i2) hc0
    | deposit _ _ _ _ _ _ _ _ _ => exact ⟨i1, i2, i3, i4, i5, i6⟩
    | withdraw _ _ _ _ _ _ _ _ => exact ⟨i1, i2, i3, i4, i5, i6⟩
    | chargeZero _ _ => exact ⟨i1, i2, i3, i4, i5, i6⟩
    | charge _ _ _ _ _ _ _ => exact ⟨i1, i2, i3, i4, i5, i6⟩
    | sweepZero _ _ _ => exact ⟨i1, i2, i3, i4, i5, i6⟩
    | sweep _ _ _ _ => exact ⟨i1, i2, i3, i4, i5, i6⟩
    | transferOwnership hc0 hc => exact absurd (hc.trans i2) hc0
    | acceptOwnership hc0 hpc => exact absurd (hpc.symm.trans i3) hc0
    | renounceOwnership hc0 hc => exact absurd (hc.trans i2) hc0

/-- The environment of the witnesses: every chain's diamond is `9`, its admin `10`, and every
transfer succeeds. -/
private def envW : Env := ⟨fun _ => 9, fun _ => 10, fun _ _ _ => true, fun _ _ _ => true⟩

/-- Discharge the concrete side conditions of the witnesses. -/
local macro "wit" : tactic =>
  `(tactic| first
    | rfl
    | decide
    | (simp [fresh, setBal, bump, clear, MAX, ETH, envW]; done)
    | (norm_num [fresh, setBal, bump, clear, MAX, ETH, envW]; done))

theorem UncheckedChargeDrains : Properties.UncheckedChargeDrains := by
  let s : State := { fresh with feeToken := ETH, feePerUnit := 3, bal := fun _ _ => 100 }
  have hstep : ChargeNoCallerCheck envW s (.charge 13 7 1 10) _ :=
    .charge (by wit) (by wit) (by wit) (by wit) (by wit) (by wit)
  have hlt : setBal s.bal 7 s.feeToken (s.bal 7 s.feeToken - s.feePerUnit * 10) 7 s.feeToken <
      s.bal 7 s.feeToken := by
    rw [setBal_same]; show 100 - 3 * 10 < 100; omega
  refine ⟨envW, s, _, 13, 7, 1, 10, hstep, by decide, by decide, hlt, ?_⟩
  intro h
  rcases DebitAuthority envW s _ _ 7 s.feeToken h hlt with ⟨dst, a, hl, _⟩ | ⟨b, u, hl, _⟩
  · cases hl
  · injection hl with h1
    exact absurd h1 (by decide)

theorem FeeFlowWitness : Properties.FeeFlowWitness := by
  refine ⟨_, .step (.step (.step (.step (.step (.step .refl
      (.init (E := envW) (caller := 4) (o := 5) (r := 6)
        (by wit) (by wit) (by wit) (by wit) (by wit)))
      (.setFee (E := envW) (caller := 5) (tok := ETH) (f := 3)
        (by wit) (by wit) (by wit) (by wit)))
      (.deposit (E := envW) (caller := 8) (c := 7) (tok := ETH) (a := 100) (v := 100)
        (by wit) (by wit) (by wit) (by wit) (by wit) (by wit) (by wit) (by wit)
        (fun h => absurd rfl h)))
      (.charge (E := envW) (caller := 9) (c := 7) (b := 1) (u := 10)
        (by wit) (by wit) (by wit) (by wit) (by wit) (by wit) (by wit)))
      (.sweep (E := envW) (caller := 11) (tok := ETH)
        (by wit) (by wit) (by wit) (by wit)))
      (.withdraw (E := envW) (caller := 10) (c := 7) (tok := ETH) (dst := 12) (a := 70)
        (by wit) (by wit) (by wit) (by wit) (by wit) (by wit) (by wit) (by wit)),
    ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wit

end Contracts.L1InteropFeeManager
