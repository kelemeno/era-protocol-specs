import EraSpec.Contracts.InteropCenter.Properties.FeeState

/-!
# Proofs: the `InteropCenter` fee state at draft/v0.35.0

Every per-transaction statement is a case split on `exec`. The run statements follow from a
per-step relation that is reflexive and transitive (`run_rel`):

* native backing: `S'.bal + Σ S.protocolFees + S.forcedIn = S.bal + Σ S'.protocolFees +
  S'.forcedIn` (`native_step`), an equality because a send's `msg.value` is exactly its payments
  plus its fee (`msgValue_split`) and a claim pays exactly the entry it zeroes;
* ZK backing: `zkBalance S + Σ S'.zkFees ≤ zkBalance S' + Σ S.zkFees` (`zk_step`), an inequality
  because a token inflow, a claim to the center itself and the first caching of `zkToken` may
  raise the balance without touching the ledger;
* the counter: the log and the leaves are extended, and the counter grows by the L2→L2 call count
  of the new log entries (`units_step`).
-/

namespace Contracts.InteropCenter.FeeState

open Contracts.InteropCenter (Word Address CallStarter totalBurnedCallsValue)

/-! ## Ledger sums -/

private theorem sum_update_add (f : Address → ℕ) (i : Address) (v : ℕ) :
    (∑ a : Address, Function.update f i v a) + f i = (∑ a : Address, f a) + v := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i) f v, Finset.sdiff_singleton_eq_erase]
  have he := Finset.sum_erase_add (Finset.univ : Finset Address) f (Finset.mem_univ i)
  omega

private theorem sum_update_plus (f : Address → ℕ) (i : Address) (v : ℕ) :
    (∑ a : Address, Function.update f i (f i + v) a) = (∑ a : Address, f a) + v := by
  have h := sum_update_add f i (f i + v)
  omega

private theorem sum_update_zero (f : Address → ℕ) (i : Address) :
    (∑ a : Address, Function.update f i 0 a) + f i = ∑ a : Address, f a := by
  have h := sum_update_add f i 0
  rw [Nat.add_zero] at h
  exact h

private theorem le_sum (f : Address → ℕ) (i : Address) : f i ≤ ∑ a : Address, f a :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

private theorem sum_eq_zero_iff (f : Address → ℕ) : (∑ a : Address, f a) = 0 ↔ ∀ a, f a = 0 := by
  simp [Finset.sum_eq_zero_iff]

/-! ## Payments -/

theorem nativeOut_append (a b : List Payment) :
    nativeOut (a ++ b) = nativeOut a + nativeOut b := by
  simp [nativeOut]

theorem nativeOut_forwardPayments (l : List CallStarter) :
    nativeOut (forwardPayments l) = indirectTotal l := by
  induction l with
  | nil => rfl
  | cons cs rest ih =>
    by_cases h : cs.callAttributes.indirectCall = true
    · simp only [forwardPayments, indirectTotal, nativeOut, List.filter_cons, h, ite_true,
        List.map_cons, List.sum_cons, forwardOf, Payment.nativeValue] at ih ⊢
      omega
    · simp only [forwardPayments, indirectTotal, nativeOut, List.filter_cons, h,
        Bool.false_eq_true, ite_false] at ih ⊢
      exact ih

theorem nativeOut_valuePayment (P : Params) (inp : SendInput) :
    nativeOut (valuePayment P inp) =
      if sameBase P inp = true then totalBurnedCallsValue inp.starters else 0 := by
  unfold valuePayment
  by_cases h0 : totalBurnedCallsValue inp.starters = 0
  · simp [h0, nativeOut]
  · by_cases hb : sameBase P inp = true
    · simp [h0, hb, nativeOut, Payment.nativeValue]
    · simp [h0, hb, nativeOut, Payment.nativeValue]

theorem nativeOut_sendPayments (P : Params) (inp : SendInput) :
    nativeOut (sendPayments P inp) = indirectTotal inp.starters +
      (if sameBase P inp = true then totalBurnedCallsValue inp.starters else 0) := by
  rw [sendPayments, nativeOut_append, nativeOut_forwardPayments, nativeOut_valuePayment]

/-- **THE `msg.value` SPLIT.** With the equalities, `msg.value` is the native value paid out plus
the protocol fee. -/
theorem msgValue_split {K : Checks} {P : Params} {S : State} {inp : SendInput}
    (hK : K.valueCheck = true) (h : SendOk K P S inp) :
    inp.msgValue = nativeOut (sendPayments P inp) + protocolFeeOf S inp := by
  have hv := h.2.2.2.2.2.2.1 hK
  rw [nativeOut_sendPayments, hv, expectedValue]
  by_cases hb : sameBase P inp = true
  · simp only [hb, ite_true]; omega
  · simp only [hb, Bool.false_eq_true, ite_false]; omega

/-! ## The send step -/

theorem exec_send_iff {K : Checks} {P : Params} {S : State} {inp : SendInput} {S' : State} :
    exec K P (.send inp) S = some S' ↔ SendOk K P S inp ∧ afterSend P S inp = S' := by
  simp only [exec]
  split_ifs with h
  · simp [h]
  · simp [h]

/-- With `SendOk`, the ZK token the fixed-fee path uses is a standard token under the premise. -/
theorem fixed_token_standard {K : Checks} {P : Params} {S : State} {inp : SendInput}
    (hP : StandardTokens P) (h : SendOk K P S inp) (hf : fixedFeePath S inp = true) :
    P.tokenCode (zkTokenFor S inp.zkResolved) = .standard := by
  have hz := h.2.2.2.2.2.2.2.1 hf
  cases hc : P.tokenCode (zkTokenFor S inp.zkResolved) with
  | standard => rfl
  | noTransfer => rw [hc] at hz; simp [TokenCode.hasTransfer] at hz
  | nonStandard f => exact absurd hc (hP _ f)

theorem SendOk.funded {K : Checks} {P : Params} {S : State} {inp : SendInput}
    (h : SendOk K P S inp) : nativeOut (sendPayments P inp) ≤ S.bal + inp.msgValue :=
  h.2.2.2.2.2.1

theorem SendOk.zk {K : Checks} {P : Params} {S : State} {inp : SendInput}
    (h : SendOk K P S inp) (hf : fixedFeePath S inp = true) :
    zkTokenFor S inp.zkResolved ≠ 0 ∧ (P.tokenCode (zkTokenFor S inp.zkResolved)).hasTransfer = true ∧
      inp.sender ≠ P.center :=
  h.2.2.2.2.2.2.2.1 hf

theorem SendOk.indirect {K : Checks} {P : Params} {S : State} {inp : SendInput}
    (h : SendOk K P S inp) : ∀ cs ∈ inp.starters, cs.callAttributes.indirectCall = true →
      cs.target = P.router ∧ cs.callAttributes.interopCallValue = 0 :=
  h.2.2.2.2.1

/-! ## ZK balance -/

theorem zkTokenFor_cases (S : State) (z : Address) :
    S.zkToken = 0 ∨ S.zkToken = zkTokenFor S z := by
  unfold zkTokenFor
  by_cases h : S.zkToken = 0
  · exact Or.inl h
  · right; simp [h]

theorem zkBalance_le {S : State} {t : Address} (h : S.zkToken = 0 ∨ S.zkToken = t) :
    zkBalance S ≤ S.tokBal t := by
  unfold zkBalance
  rcases h with h | h
  · simp [h]
  · split_ifs
    · exact Nat.zero_le _
    · rw [h]

theorem zkBalance_of {S : State} (h : S.zkToken ≠ 0) : zkBalance S = S.tokBal S.zkToken := by
  simp [zkBalance, h]

private theorem zkBalance_claimed (S : State) (f : Address → ℕ) (t : Address) (g : Address → ℕ)
    (cl : List ClaimRecord) (ht : t ≠ 0) :
    zkBalance { S with zkFees := f, zkToken := t, tokBal := g, claims := cl } = g t := by
  simp [zkBalance, ht]

/-! ## Runs -/

/-- A reflexive, transitive relation implied by every successful transaction holds along every
run. -/
theorem run_rel {K : Checks} {P : Params} (R : State → State → Prop) (hrefl : ∀ S, R S S)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (hstep : ∀ tx S S', exec K P tx S = some S' → R S S') :
    ∀ txs S S', run K P txs S = some S' → R S S' := by
  intro txs
  induction txs with
  | nil =>
    intro S S' h
    simp only [run, Option.some.injEq] at h
    subst h
    exact hrefl S
  | cons tx rest ih =>
    intro S S' h
    simp only [run] at h
    cases hx : exec K P tx S with
    | none => rw [hx] at h; exact absurd h (by simp)
    | some S1 =>
      rw [hx] at h
      exact htrans _ _ _ (hstep _ _ _ hx) (ih _ _ h)

/-! ## (1) Backing, per step -/

/-- **THE NATIVE STEP.** With the equalities, every transaction keeps
`bal - Σ protocolFees - forcedIn` fixed. -/
theorem native_step {K : Checks} {P : Params} {tx : Tx} {S S' : State} (hK : K.valueCheck = true)
    (h : exec K P tx S = some S') :
    S'.bal + (∑ c : Address, S.protocolFees c) + S.forcedIn =
      S.bal + (∑ c : Address, S'.protocolFees c) + S'.forcedIn := by
  cases tx with
  | send inp =>
    obtain ⟨hok, rfl⟩ := exec_send_iff.mp h
    have hv := msgValue_split hK hok
    have hs := sum_update_plus S.protocolFees inp.coinbase (protocolFeeOf S inp)
    simp only [afterSend]
    rw [hs]
    omega
  | preview c => simp [exec] at h
  | claimProtocolFees c r =>
    simp only [exec, claimProtocolFeesStep] at h
    split_ifs at h with h1 h2 h3
    · cases h; rfl
    · cases h
      have hz := sum_update_zero S.protocolFees c
      simp only
      omega
  | claimZKFees c r z =>
    simp only [exec, claimZKFeesStep, claimZKFeesBody] at h
    split_ifs at h <;> cases h <;> rfl
  | setInteropFee c f =>
    simp only [exec] at h
    split_ifs at h; cases h; rfl
  | nativeInflow x =>
    simp only [exec, Option.some.injEq] at h
    subst h
    simp only
    omega
  | tokenInflow t x =>
    simp only [exec, Option.some.injEq] at h
    subst h
    rfl
  | _ =>
    simp only [exec, initL2Step] at h
    split_ifs at h <;> cases h <;> rfl

theorem forcedIn_mono {K : Checks} {P : Params} {tx : Tx} {S S' : State}
    (h : exec K P tx S = some S') : S.forcedIn ≤ S'.forcedIn := by
  cases tx with
  | send inp => obtain ⟨_, rfl⟩ := exec_send_iff.mp h; exact le_refl _
  | preview c => simp [exec] at h
  | claimProtocolFees c r =>
    simp only [exec, claimProtocolFeesStep] at h
    split_ifs at h <;> cases h <;> exact le_refl _
  | claimZKFees c r z =>
    simp only [exec, claimZKFeesStep, claimZKFeesBody] at h
    split_ifs at h <;> cases h <;> exact le_refl _
  | nativeInflow x =>
    simp only [exec, Option.some.injEq] at h
    subst h
    exact Nat.le_add_right _ _
  | tokenInflow t x =>
    simp only [exec, Option.some.injEq] at h
    subst h
    exact le_refl _
  | _ =>
    simp only [exec, initL2Step] at h
    split_ifs at h <;> cases h <;> exact le_refl _

/-- **THE ZK STEP.** Under the standard-token premise, no transaction lowers
`zkBalance - Σ zkFees`. -/
theorem zk_step {K : Checks} {P : Params} {tx : Tx} {S S' : State} (hP : StandardTokens P)
    (h : exec K P tx S = some S') :
    zkBalance S + (∑ c : Address, S'.zkFees c) ≤ zkBalance S' + (∑ c : Address, S.zkFees c) := by
  cases tx with
  | send inp =>
    obtain ⟨hok, rfl⟩ := exec_send_iff.mp h
    by_cases hf : fixedFeePath S inp = true
    · have hz := hok.zk hf
      have hstd := fixed_token_standard hP hok hf
      have hs := sum_update_plus S.zkFees inp.coinbase (zkFeeOf S inp)
      have hle := zkBalance_le (zkTokenFor_cases S inp.zkResolved)
      have hb : zkBalance (afterSend P S inp) =
          S.tokBal (zkTokenFor S inp.zkResolved) + zkFeeOf S inp := by
        rw [zkBalance_of (by simp only [afterSend, hf, ite_true]; exact hz.1)]
        simp only [afterSend, hf, ite_true, Function.update_self, hstd, TokenCode.credited]
      rw [hb]
      simp only [afterSend, hf, ite_true]
      rw [hs]
      omega
    · have hf' : fixedFeePath S inp = false := by simpa using hf
      have hb : zkBalance (afterSend P S inp) = zkBalance S := by
        simp only [zkBalance, afterSend, hf', Bool.false_eq_true, ite_false]
      rw [hb]
      simp only [afterSend, hf', Bool.false_eq_true, ite_false]
      exact le_refl _
  | preview c => simp [exec] at h
  | claimZKFees c r z =>
    simp only [exec, claimZKFeesStep, claimZKFeesBody] at h
    split_ifs at h with h1 h2 h3 hr
    · cases h; exact le_refl _
    · cases h
      obtain ⟨ht0, _, hcov⟩ := h3
      have hz := sum_update_zero S.zkFees c
      have hle := zkBalance_le (zkTokenFor_cases S z)
      rw [zkBalance_claimed _ _ _ _ _ ht0]
      dsimp only
      omega
    · cases h
      obtain ⟨ht0, _, hcov⟩ := h3
      have hz := sum_update_zero S.zkFees c
      have hle := zkBalance_le (zkTokenFor_cases S z)
      rw [zkBalance_claimed _ _ _ _ _ ht0, Function.update_self]
      dsimp only
      omega
  | claimProtocolFees c r =>
    simp only [exec, claimProtocolFeesStep] at h
    split_ifs at h <;> cases h <;> exact le_refl _
  | tokenInflow t x =>
    simp only [exec, Option.some.injEq] at h
    subst h
    have hb : zkBalance S ≤ zkBalance
        { S with tokBal := Function.update S.tokBal t (S.tokBal t + x) } := by
      unfold zkBalance
      split_ifs with h0
      · exact le_refl _
      · by_cases ht : S.zkToken = t
        · subst ht; simp
        · simp [Function.update_of_ne ht]
    simp only at hb ⊢
    omega
  | nativeInflow x =>
    simp only [exec, Option.some.injEq] at h
    subst h
    exact le_refl _
  | _ =>
    simp only [exec, initL2Step] at h
    split_ifs at h <;> cases h <;> exact le_refl _

/-! ## (1) Backing, along runs -/

theorem NativeBalanceIsFeesPlusForced : Properties.NativeBalanceIsFeesPlusForced := by
  intro K P S hK ⟨txs, h⟩
  have key := run_rel (K := K) (P := P)
    (fun a b => b.bal + (∑ c : Address, a.protocolFees c) + a.forcedIn =
      a.bal + (∑ c : Address, b.protocolFees c) + b.forcedIn)
    (fun _ => rfl) (fun a b c hab hbc => by omega) (fun _ _ _ h => native_step hK h) txs init S h
  simp only [init, Finset.sum_const_zero, add_zero, zero_add] at key
  omega

theorem ProtocolFeesBacked : Properties.ProtocolFeesBacked := by
  intro K P S hK hR
  have := NativeBalanceIsFeesPlusForced K P S hK hR
  omega

theorem ZkFeesBacked : Properties.ZkFeesBacked := by
  intro K P S hP ⟨txs, h⟩
  have key := run_rel (K := K) (P := P)
    (fun a b => zkBalance a + (∑ c : Address, b.zkFees c) ≤ zkBalance b + (∑ c : Address, a.zkFees c))
    (fun _ => le_refl _) (fun a b c hab hbc => by omega) (fun _ _ _ h => zk_step hP h) txs init S h
  have h0 : zkBalance init = 0 := rfl
  have hs : (∑ c : Address, init.zkFees c) = 0 := by simp [init]
  rw [h0, hs] at key
  refine ⟨fun hz c => ?_, by omega⟩
  have hb : zkBalance S = 0 := by simp [zkBalance, hz]
  have := le_sum S.zkFees c
  omega

theorem BackingNeverShrinks : Properties.BackingNeverShrinks := by
  intro K P tx S S' h
  refine ⟨fun hK => ?_, fun hP => ?_⟩
  · have h1 := native_step hK h
    have h2 := forcedIn_mono h
    rw [← Nat.cast_sum, ← Nat.cast_sum]
    omega
  · have h1 := zk_step hP h
    rw [← Nat.cast_sum, ← Nat.cast_sum]
    omega

/-! ## (2) One send -/

theorem SendAccruesExactProtocolFee : Properties.SendAccruesExactProtocolFee := by
  intro K P S inp S' hK h
  obtain ⟨hok, rfl⟩ := exec_send_iff.mp h
  have hv := msgValue_split hK hok
  refine ⟨?_, ?_, ?_⟩
  · simp only [afterSend]
    omega
  · simp [afterSend]
  · intro c hc
    simp [afterSend, Function.update_of_ne hc]

theorem SendAccruesExactZkFee : Properties.SendAccruesExactZkFee := by
  intro K P S inp S' hP h
  obtain ⟨hok, rfl⟩ := exec_send_iff.mp h
  constructor
  · intro hf
    have hz := hok.zk hf
    have hstd := fixed_token_standard hP hok hf
    refine ⟨by simp [afterSend, hf], by simpa [afterSend, hf] using hz.1, ?_, ?_⟩
    · simp [afterSend, hf, hstd, TokenCode.credited, zkFeeOf]
    · simp [afterSend, hf, zkFeeOf]
  · intro hf
    simp [afterSend, hf]

/-- With the indirect-starter restriction, the calls' value is the sum over the direct
starters. -/
theorem burned_eq_direct (l : List CallStarter)
    (h : ∀ cs ∈ l, cs.callAttributes.indirectCall = true → cs.callAttributes.interopCallValue = 0) :
    totalBurnedCallsValue l =
      ((l.filter fun cs => !cs.callAttributes.indirectCall).map
        fun cs => cs.callAttributes.interopCallValue).sum := by
  induction l with
  | nil => rfl
  | cons cs rest ih =>
    have ih' := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
    simp only [totalBurnedCallsValue, List.map_cons, List.sum_cons] at ih' ⊢
    by_cases hi : cs.callAttributes.indirectCall = true
    · have h0 := h cs (List.mem_cons_self ..) hi
      simp [hi, h0, ih']
    · simp [hi, ih']

theorem SendPaymentsExact : Properties.SendPaymentsExact := by
  intro K P S inp S' h
  obtain ⟨hok, rfl⟩ := exec_send_iff.mp h
  refine ⟨rfl, ?_, nativeOut_forwardPayments _, burned_eq_direct _ ?_, ?_, ?_,
    fun hK => msgValue_split hK hok⟩
  · intro p hp
    simp only [forwardPayments, List.mem_map, List.mem_filter] at hp
    obtain ⟨cs, ⟨hcs, hind⟩, rfl⟩ := hp
    exact ⟨_, by rw [forwardOf, (hok.indirect cs hcs hind).1]⟩
  · intro cs hcs hind
    exact (hok.indirect cs hcs hind).2
  · constructor
    · rintro ⟨v, hv⟩
      simp only [sendPayments, List.mem_append] at hv
      rcases hv with hv | hv
      · simp [forwardPayments, forwardOf] at hv
      · unfold valuePayment at hv
        split_ifs at hv with h0 hb <;> simp_all
    · rintro ⟨hb, h0⟩
      exact ⟨totalBurnedCallsValue inp.starters, by simp [sendPayments, valuePayment, h0, hb]⟩
  · constructor
    · rintro ⟨a, o, v, hv⟩
      simp only [sendPayments, List.mem_append] at hv
      rcases hv with hv | hv
      · simp [forwardPayments, forwardOf] at hv
      · unfold valuePayment at hv
        split_ifs at hv with h0 hb <;> simp_all
    · rintro ⟨hb, h0⟩
      exact ⟨inp.destBase, inp.sender, totalBurnedCallsValue inp.starters,
        by simp [sendPayments, valuePayment, h0, hb]⟩

/-! ## (3) Claims -/

private theorem update_zero_of_zero (f : Address → ℕ) (c : Address) (h : f c = 0) :
    f = Function.update f c 0 := by
  funext x
  by_cases hx : x = c
  · subst hx; simp [h]
  · simp [Function.update_of_ne hx]

theorem ClaimProtocolFeesExact : Properties.ClaimProtocolFeesExact := by
  intro K P S c r S' h
  simp only [exec, claimProtocolFeesStep] at h
  split_ifs at h with h1 h2 h3
  · cases h
    exact ⟨update_zero_of_zero _ _ h2, by simp [h2], by simp [h2], fun _ => rfl,
      fun hne => absurd h2 hne⟩
  · cases h
    exact ⟨rfl, rfl, h3.1, fun h0 => absurd h0 h2, fun _ => ⟨h3.2, rfl⟩⟩

theorem ClaimZkFeesExact : Properties.ClaimZkFeesExact := by
  intro K P S c r z S' h
  simp only [exec, claimZKFeesStep, claimZKFeesBody] at h
  split_ifs at h with h1 h2 h3 hr
  · cases h
    exact ⟨update_zero_of_zero _ _ h2, fun _ => rfl, fun hne => absurd h2 hne⟩
  · cases h
    exact ⟨rfl, fun h0 => absurd h0 h2,
      fun _ => ⟨rfl, h3.2.2, rfl, fun hne => absurd hr hne, fun _ => rfl⟩⟩
  · cases h
    exact ⟨rfl, fun h0 => absurd h0 h2,
      fun _ => ⟨rfl, h3.2.2, rfl, fun _ => rfl, fun he => absurd he hr⟩⟩

/-! ## (4) Writers -/

theorem ProtocolFeeSetOnlyByBootloader : Properties.ProtocolFeeSetOnlyByBootloader := by
  intro K P tx S S' h
  cases tx with
  | send inp => obtain ⟨_, rfl⟩ := exec_send_iff.mp h; exact Or.inl rfl
  | setInteropFee c f =>
    simp only [exec] at h
    split_ifs at h with hc
    cases h
    exact Or.inr ⟨f, by rw [hc], rfl⟩
  | preview c => simp [exec] at h
  | claimProtocolFees c r =>
    simp only [exec, claimProtocolFeesStep] at h
    split_ifs at h <;> cases h <;> exact Or.inl rfl
  | claimZKFees c r z =>
    simp only [exec, claimZKFeesStep, claimZKFeesBody] at h
    split_ifs at h <;> cases h <;> exact Or.inl rfl
  | nativeInflow x =>
    simp only [exec, Option.some.injEq] at h; subst h; exact Or.inl rfl
  | tokenInflow t x =>
    simp only [exec, Option.some.injEq] at h; subst h; exact Or.inl rfl
  | _ =>
    simp only [exec, initL2Step] at h
    split_ifs at h <;> cases h <;> exact Or.inl rfl

theorem InitFieldsOnlyByInitL2 : Properties.InitFieldsOnlyByInitL2 := by
  intro K P tx S S' h
  cases tx with
  | send inp => obtain ⟨_, rfl⟩ := exec_send_iff.mp h; exact Or.inl ⟨rfl, rfl, rfl⟩
  | initL2 c l o z =>
    simp only [exec, initL2Step] at h
    split_ifs at h with hg
    all_goals
      cases h
      obtain ⟨hc, hl, hz, _⟩ := hg
      exact Or.inr ⟨l, o, z, by rw [hc], hl, hz, rfl, rfl, rfl⟩
  | preview c => simp [exec] at h
  | claimProtocolFees c r =>
    simp only [exec, claimProtocolFeesStep] at h
    split_ifs at h <;> cases h <;> exact Or.inl ⟨rfl, rfl, rfl⟩
  | claimZKFees c r z =>
    simp only [exec, claimZKFeesStep, claimZKFeesBody] at h
    split_ifs at h <;> cases h <;> exact Or.inl ⟨rfl, rfl, rfl⟩
  | nativeInflow x =>
    simp only [exec, Option.some.injEq] at h; subst h; exact Or.inl ⟨rfl, rfl, rfl⟩
  | tokenInflow t x =>
    simp only [exec, Option.some.injEq] at h; subst h; exact Or.inl ⟨rfl, rfl, rfl⟩
  | _ =>
    simp only [exec] at h
    split_ifs at h
    cases h
    exact Or.inl ⟨rfl, rfl, rfl⟩

/-- A send or a claim needs the initialised, unentered lock. -/
theorem lock_of_sendOrClaim {K : Checks} {P : Params} {tx : Tx} {S S' : State}
    (h : exec K P tx S = some S') (hsc : tx.isSendOrClaim = true) : S.lock = 1 := by
  cases tx with
  | send inp => exact (exec_send_iff.mp h).1.1
  | claimProtocolFees c r =>
    simp only [exec, claimProtocolFeesStep] at h
    split_ifs at h with h1
    all_goals exact h1
  | claimZKFees c r z =>
    simp only [exec, claimZKFeesStep, claimZKFeesBody] at h
    split_ifs at h with h1
    all_goals exact h1
  | _ => simp [Tx.isSendOrClaim] at hsc

/-- Every transaction other than `initL2` leaves the lock slot as it found it. -/
theorem lock_preserved {K : Checks} {P : Params} {tx : Tx} {S S' : State}
    (h : exec K P tx S = some S') (hi : tx.isInitL2 = false) : S'.lock = S.lock := by
  cases tx with
  | send inp => obtain ⟨_, rfl⟩ := exec_send_iff.mp h; rfl
  | initL2 c l o z => simp [Tx.isInitL2] at hi
  | preview c => simp [exec] at h
  | claimProtocolFees c r =>
    simp only [exec, claimProtocolFeesStep] at h
    split_ifs at h <;> cases h <;> rfl
  | claimZKFees c r z =>
    simp only [exec, claimZKFeesStep, claimZKFeesBody] at h
    split_ifs at h <;> cases h <;> rfl
  | nativeInflow x =>
    simp only [exec, Option.some.injEq] at h; subst h; rfl
  | tokenInflow t x =>
    simp only [exec, Option.some.injEq] at h; subst h; rfl
  | _ =>
    simp only [exec] at h
    split_ifs at h
    cases h
    rfl

/-- `initL2` needs the uninitialised lock and leaves it initialised. -/
theorem lock_of_initL2 {K : Checks} {P : Params} {tx : Tx} {S S' : State}
    (h : exec K P tx S = some S') (hi : tx.isInitL2 = true) : S.lock = 0 ∧ S'.lock = 1 := by
  cases tx with
  | initL2 c l o z =>
    simp only [exec, initL2Step] at h
    split_ifs at h with hg
    all_goals
      cases h
      exact ⟨hg.2.1, rfl⟩
  | _ => simp [Tx.isInitL2] at hi

/-- From the initialised lock, no transaction of a run is an `initL2`. -/
private theorem no_initL2_after {K : Checks} {P : Params} :
    ∀ (txs : List Tx) (S S' : State), S.lock = 1 → run K P txs S = some S' →
      txs.filter Tx.isInitL2 = [] := by
  intro txs
  induction txs with
  | nil => intro _ _ _ _; rfl
  | cons tx rest ih =>
    intro S S' hl h
    simp only [run] at h
    cases hx : exec K P tx S with
    | none => rw [hx] at h; exact absurd h (by simp)
    | some S1 =>
      rw [hx] at h
      cases hi : tx.isInitL2 with
      | true => have := (lock_of_initL2 hx hi).1; omega
      | false =>
        rw [List.filter_cons_of_neg (by simp [hi])]
        exact ih S1 S' (by rw [lock_preserved hx hi, hl]) h

private theorem init_order {K : Checks} {P : Params} :
    ∀ (txs : List Tx) (S S' : State), S.lock = 0 → run K P txs S = some S' →
      (txs.filter Tx.isInitL2).length ≤ 1 ∧
      ∀ (i : ℕ) (hi : i < txs.length), txs[i].isSendOrClaim = true →
        ∃ (j : ℕ) (hj : j < i), (txs[j]'(Nat.lt_trans hj hi)).isInitL2 = true := by
  intro txs
  induction txs with
  | nil => intro _ _ _ _; exact ⟨by simp, fun i hi => absurd hi (by simp)⟩
  | cons tx rest ih =>
    intro S S' hl h
    simp only [run] at h
    cases hx : exec K P tx S with
    | none => rw [hx] at h; exact absurd h (by simp)
    | some S1 =>
      rw [hx] at h
      cases hi : tx.isInitL2 with
      | true =>
        have hl1 := (lock_of_initL2 hx hi).2
        have hnone := no_initL2_after rest S1 S' hl1 h
        refine ⟨by rw [List.filter_cons_of_pos (by simp [hi]), hnone]; simp, ?_⟩
        intro i hi' hsc
        cases i with
        | zero =>
          simp only [List.getElem_cons_zero] at hsc
          cases tx <;> simp_all [Tx.isSendOrClaim, Tx.isInitL2]
        | succ k => exact ⟨0, Nat.succ_pos k, by simpa using hi⟩
      | false =>
        have hsc0 : tx.isSendOrClaim = false := by
          cases hs : tx.isSendOrClaim with
          | false => rfl
          | true => have := lock_of_sendOrClaim hx hs; omega
        have hl1 : S1.lock = 0 := by rw [lock_preserved hx hi, hl]
        obtain ⟨hcount, hord⟩ := ih S1 S' hl1 h
        refine ⟨by rw [List.filter_cons_of_neg (by simp [hi])]; exact hcount, ?_⟩
        intro i hi' hsc
        cases i with
        | zero =>
          simp only [List.getElem_cons_zero] at hsc
          rw [hsc0] at hsc
          exact absurd hsc (by simp)
        | succ k =>
          simp only [List.getElem_cons_succ] at hsc
          obtain ⟨j, hj, hjinit⟩ := hord k (by simpa using hi') hsc
          exact ⟨j + 1, Nat.succ_lt_succ hj, by simpa using hjinit⟩

theorem InitL2AtMostOnceAndFirst : Properties.InitL2AtMostOnceAndFirst := by
  intro K P txs S h
  exact init_order txs init S rfl h

theorem ZkTokenSetOnce : Properties.ZkTokenSetOnce := by
  intro K P tx S S' h hz
  cases tx with
  | send inp =>
    obtain ⟨_, rfl⟩ := exec_send_iff.mp h
    simp only [afterSend, zkTokenFor, hz, ite_false]
    split_ifs <;> rfl
  | claimZKFees c r z =>
    simp only [exec, claimZKFeesStep, claimZKFeesBody] at h
    split_ifs at h <;> cases h <;> simp [zkTokenFor, hz]
  | preview c => simp [exec] at h
  | claimProtocolFees c r =>
    simp only [exec, claimProtocolFeesStep] at h
    split_ifs at h <;> cases h <;> rfl
  | nativeInflow x =>
    simp only [exec, Option.some.injEq] at h; subst h; rfl
  | tokenInflow t x =>
    simp only [exec, Option.some.injEq] at h; subst h; rfl
  | _ =>
    simp only [exec, initL2Step] at h
    split_ifs at h <;> cases h <;> rfl

theorem PausedNeverWritten : Properties.PausedNeverWritten := by
  intro K P tx S S' h
  cases tx with
  | send inp => obtain ⟨_, rfl⟩ := exec_send_iff.mp h; rfl
  | preview c => simp [exec] at h
  | claimProtocolFees c r =>
    simp only [exec, claimProtocolFeesStep] at h
    split_ifs at h <;> cases h <;> rfl
  | claimZKFees c r z =>
    simp only [exec, claimZKFeesStep, claimZKFeesBody] at h
    split_ifs at h <;> cases h <;> rfl
  | nativeInflow x =>
    simp only [exec, Option.some.injEq] at h; subst h; rfl
  | tokenInflow t x =>
    simp only [exec, Option.some.injEq] at h; subst h; rfl
  | _ =>
    simp only [exec, initL2Step] at h
    split_ifs at h <;> cases h <;> rfl

theorem OwnerHasNoFeePower : Properties.OwnerHasNoFeePower := by
  refine ⟨?_, ?_⟩
  · intro K P tx S S' hown h
    cases tx with
    | transferOwnership c o =>
      simp only [exec] at h
      split_ifs at h
      cases h
      exact ⟨S.owner, o, rfl⟩
    | acceptOwnership c =>
      simp only [exec] at h
      split_ifs at h
      cases h
      exact ⟨c, 0, rfl⟩
    | renounceOwnership c =>
      simp only [exec] at h
      split_ifs at h
      cases h
      exact ⟨0, 0, rfl⟩
    | _ => simp [Tx.isOwnership] at hown
  · intro K P tx S o p hown hinit
    cases tx with
    | send inp =>
      have hiff : SendOk K P (S.withOwners o p) inp ↔ SendOk K P S inp := Iff.rfl
      simp only [exec]
      by_cases hok : SendOk K P S inp
      · simp only [hok, hiff.mpr hok, ite_true, Option.map_some]
        rfl
      · simp only [hok, (not_congr hiff).mpr hok, ite_false, Option.map_none]
    | preview c => rfl
    | claimProtocolFees c r =>
      simp only [exec, claimProtocolFeesStep, State.withOwners]
      by_cases h1 : S.lock = 1 <;> by_cases h2 : S.protocolFees c = 0 <;>
        by_cases h3 : S.protocolFees c ≤ S.bal ∧ r ≠ P.center <;> simp [h1, h2, h3]
    | claimZKFees c r z =>
      have ht : zkTokenFor (S.withOwners o p) z = zkTokenFor S z := rfl
      simp only [exec, claimZKFeesStep, claimZKFeesBody, ht]
      generalize zkTokenFor S z = t
      by_cases h1 : S.lock = 1 <;> by_cases h2 : S.zkFees c = 0 <;>
        by_cases h3 : t ≠ 0 ∧ (P.tokenCode t).hasTransfer = true ∧ S.zkFees c ≤ S.tokBal t <;>
        by_cases hr : r = P.center <;> simp [h1, h2, h3, hr, State.withOwners]
    | setInteropFee c f =>
      simp only [exec]
      by_cases hc : c = P.bootloader <;> simp [hc, State.withOwners]
    | initL2 c l o' z => simp [Tx.isInitL2] at hinit
    | forwardTransactionOnGateway c =>
      simp only [exec]
      by_cases hc : c = P.relaySender <;> simp [hc]
    | transferOwnership c o' => simp [Tx.isOwnership] at hown
    | acceptOwnership c => simp [Tx.isOwnership] at hown
    | renounceOwnership c => simp [Tx.isOwnership] at hown
    | foreignAppend c m =>
      simp only [exec]
      by_cases hc : c ≠ P.center ∧ K.onlyInteropCenter = false <;> simp [hc, State.withOwners]
    | nativeInflow x => rfl
    | tokenInflow t x => rfl

/-! ## (5) The fee-unit counter -/

theorem FeeUnitsDeltaExact : Properties.FeeUnitsDeltaExact := by
  intro K P tx S S' h
  suffices hd : S'.feeUnits = S.feeUnits + tx.unitsFrom S from ⟨hd, by omega⟩
  cases tx with
  | send inp =>
    obtain ⟨_, rfl⟩ := exec_send_iff.mp h
    simp only [afterSend, Tx.unitsFrom]
    split_ifs <;> rfl
  | preview c => simp [exec] at h
  | claimProtocolFees c r =>
    simp only [exec, claimProtocolFeesStep] at h
    split_ifs at h <;> cases h <;> rfl
  | claimZKFees c r z =>
    simp only [exec, claimZKFeesStep, claimZKFeesBody] at h
    split_ifs at h <;> cases h <;> rfl
  | nativeInflow x =>
    simp only [exec, Option.some.injEq] at h; subst h; rfl
  | tokenInflow t x =>
    simp only [exec, Option.some.injEq] at h; subst h; rfl
  | _ =>
    simp only [exec, initL2Step] at h
    split_ifs at h <;> cases h <;> rfl

theorem EveryLeafCounted : Properties.EveryLeafCounted := by
  intro K P tx S S' hK h
  cases tx with
  | send inp =>
    obtain ⟨_, rfl⟩ := exec_send_iff.mp h
    by_cases hd : inp.dest = S.l1ChainId
    · exact Or.inl ⟨by simp [afterSend, hd], by simp [afterSend, hd]⟩
    · exact Or.inr ⟨inp, rfl, hd, by simp [afterSend, hd], by simp [afterSend, hd]⟩
  | foreignAppend c m =>
    simp only [exec] at h
    split_ifs at h with hg
    · rw [hK] at hg; exact absurd hg.2 (by simp)
  | preview c => simp [exec] at h
  | claimProtocolFees c r =>
    simp only [exec, claimProtocolFeesStep] at h
    split_ifs at h <;> cases h <;> exact Or.inl ⟨rfl, rfl⟩
  | claimZKFees c r z =>
    simp only [exec, claimZKFeesStep, claimZKFeesBody] at h
    split_ifs at h <;> cases h <;> exact Or.inl ⟨rfl, rfl⟩
  | nativeInflow x =>
    simp only [exec, Option.some.injEq] at h; subst h; exact Or.inl ⟨rfl, rfl⟩
  | tokenInflow t x =>
    simp only [exec, Option.some.injEq] at h; subst h; exact Or.inl ⟨rfl, rfl⟩
  | _ =>
    simp only [exec, initL2Step] at h
    split_ifs at h <;> cases h <;> exact Or.inl ⟨rfl, rfl⟩

theorem l2Calls_append (a b : List SendRecord) : l2Calls (a ++ b) = l2Calls a + l2Calls b := by
  simp [l2Calls, List.filter_append]

/-- One step extends the log and the leaves, and moves the counter by the new entries' L2→L2 call
count, which is also the new leaves' sum. -/
private theorem units_step {K : Checks} {P : Params} {tx : Tx} {S S' : State}
    (hK : K.onlyInteropCenter = true) (h : exec K P tx S = some S') :
    ∃ (new : List SendRecord) (nl : List ℕ), S'.log = S.log ++ new ∧ S'.leaves = S.leaves ++ nl ∧
      S'.feeUnits = S.feeUnits + l2Calls new ∧ nl.sum = l2Calls new := by
  rcases EveryLeafCounted K P tx S S' hK h with ⟨hl, hu⟩ | ⟨inp, rfl, hd, hl, hu⟩
  · -- No leaf: either a send to L1 or no send at all.
    cases tx with
    | send inp =>
      obtain ⟨_, rfl⟩ := exec_send_iff.mp h
      by_cases hd : inp.dest = S.l1ChainId
      · refine ⟨[sendRecord P S inp], [], rfl, by simp [hl], ?_, ?_⟩
        · simp [hu, l2Calls, sendRecord, hd]
        · simp [l2Calls, sendRecord, hd]
      · simp [afterSend, hd] at hl
    | foreignAppend c m =>
      simp only [exec] at h
      split_ifs at h with hg
      rw [hK] at hg
      exact absurd hg.2 (by simp)
    | preview c => simp [exec] at h
    | claimProtocolFees c r =>
      simp only [exec, claimProtocolFeesStep] at h
      split_ifs at h <;> cases h <;> exact ⟨[], [], by simp, by simp, by simp [l2Calls], rfl⟩
    | claimZKFees c r z =>
      simp only [exec, claimZKFeesStep, claimZKFeesBody] at h
      split_ifs at h <;> cases h <;> exact ⟨[], [], by simp, by simp, by simp [l2Calls], rfl⟩
    | nativeInflow x =>
      simp only [exec, Option.some.injEq] at h; subst h
      exact ⟨[], [], by simp, by simp, by simp [l2Calls], rfl⟩
    | tokenInflow t x =>
      simp only [exec, Option.some.injEq] at h; subst h
      exact ⟨[], [], by simp, by simp, by simp [l2Calls], rfl⟩
    | _ =>
      simp only [exec, initL2Step] at h
      split_ifs at h <;> cases h <;> exact ⟨[], [], by simp, by simp, by simp [l2Calls], rfl⟩
  · obtain ⟨_, rfl⟩ := exec_send_iff.mp h
    refine ⟨[sendRecord P S inp], [inp.calls], rfl, hl, ?_, ?_⟩
    · rw [hu]; simp [l2Calls, sendRecord, hd]
    · simp [l2Calls, sendRecord, hd]

theorem FeeUnitsAreL2Calls : Properties.FeeUnitsAreL2Calls := by
  intro K P txs S S' hK h
  have key := run_rel (K := K) (P := P)
    (fun a b => ∃ (new : List SendRecord) (nl : List ℕ), b.log = a.log ++ new ∧
      b.leaves = a.leaves ++ nl ∧ b.feeUnits = a.feeUnits + l2Calls new ∧ nl.sum = l2Calls new)
    (fun a => ⟨[], [], by simp, by simp, by simp [l2Calls], rfl⟩)
    (fun a b c ⟨n1, l1, h1, h2, h3, h4⟩ ⟨n2, l2, h5, h6, h7, h8⟩ =>
      ⟨n1 ++ n2, l1 ++ l2, by rw [h5, h1, List.append_assoc], by rw [h6, h2, List.append_assoc],
        by rw [h7, h3, l2Calls_append]; ring, by rw [List.sum_append, h4, h8, l2Calls_append]⟩)
    (fun _ _ _ h => units_step hK h) txs S S' h
  obtain ⟨new, nl, h1, h2, h3, h4⟩ := key
  exact ⟨new, nl, h1, h2, h3, h4, by omega⟩

/-! ## Countermodels -/

theorem wP_standard : StandardTokens wP := fun _ _ => TokenCode.noConfusion

set_option maxHeartbeats 800000 in
theorem WithoutValueCheckFeesFundAWithdrawal : Properties.WithoutValueCheckFeesFundAWithdrawal :=
  ⟨_, _, ⟨[wInit, wSetFee, .send wSendA], rfl⟩, ⟨[wInit, wSetFee, .send wSendA], rfl⟩,
    by decide, rfl, rfl, lt_of_lt_of_le (by decide) (le_sum _ 0x77), rfl⟩

set_option maxHeartbeats 800000 in
theorem NonStandardZkTokenUnbacked : Properties.NonStandardZkTokenUnbacked :=
  ⟨_, ⟨[wInit, .send wSendB], rfl⟩, lt_of_lt_of_le (by decide) (le_sum _ 0x77)⟩

set_option maxHeartbeats 800000 in
theorem ZeroCallBundleAddsLeafNoUnits : Properties.ZeroCallBundleAddsLeafNoUnits :=
  ⟨_, ⟨[wInit, .send wSendEmpty], rfl⟩, by decide⟩

theorem WithoutOnlyInteropCenterUncountedLeaf :
    Properties.WithoutOnlyInteropCenterUncountedLeaf :=
  ⟨_, ⟨[.foreignAppend 0x50 3], rfl⟩, by decide⟩

/-! ## Witnesses -/

set_option maxHeartbeats 800000 in
theorem FeeStateWitness : Properties.FeeStateWitness := by
  obtain ⟨S, hS, hbal, hf, hz77, hzb, hzk, hu, hl, hlog, hl2, hlock, hl1⟩ :
      ∃ S, run deployed wP wTxs init = some S ∧ S.bal = 8 ∧ S.forcedIn = 2 ∧
        S.zkFees 0x77 = defaultZkInteropFee ∧ zkBalance S = defaultZkInteropFee ∧
        S.zkToken = wZk ∧ S.feeUnits = 3 ∧ S.leaves = [2, 1] ∧
        S.log.map (fun r => (r.toL1, r.protocolFee, r.zkFee)) =
          [(false, 6, 0), (false, 0, defaultZkInteropFee), (true, 0, 0)] ∧
        l2Calls S.log = 3 ∧ S.lock = 1 ∧ S.l1ChainId = 1 :=
    ⟨_, rfl, by decide⟩
  have hP := NativeBalanceIsFeesPlusForced deployed wP S rfl ⟨wTxs, hS⟩
  have hZ := (ZkFeesBacked deployed wP S wP_standard ⟨wTxs, hS⟩).2
  have hle := le_sum S.zkFees 0x77
  exact ⟨S, hS, wP_standard, hbal, by omega, hf, by omega, hzb, hzk, hu, hl, hlog, hl2, hlock,
    hl1⟩

set_option maxHeartbeats 800000 in
theorem SendWitness : Properties.SendWitness :=
  ⟨_, _, _, _, rfl, rfl, rfl, rfl, by decide⟩

set_option maxHeartbeats 800000 in
theorem ClaimWitness : Properties.ClaimWitness :=
  ⟨_, _, _, rfl, rfl, by decide, rfl, by decide⟩

set_option maxHeartbeats 800000 in
theorem WriterWitness : Properties.WriterWitness :=
  ⟨_, _, rfl, rfl, by decide⟩

set_option maxHeartbeats 800000 in
theorem OwnershipWitness : Properties.OwnershipWitness :=
  ⟨_, _, _, rfl, by decide, rfl, rfl, by decide⟩

/-! ## Layout -/

theorem FeeUnitsSlotSeparate : Properties.FeeUnitsSlotSeparate := by
  refine ⟨by decide, by decide, by decide, fun n hn => ?_⟩
  unfold feeUnitsSlot
  omega

end Contracts.InteropCenter.FeeState
