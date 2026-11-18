import EraSpec.Contracts.InteropCenter.Properties.FeeReentry
import EraSpec.Contracts.InteropCenter.Proofs.FeeState

/-!
# Proofs: the fee backing with nested calls

Three mutual inductions over the call tree (`execN`, `execRun`, `buildN`):

* `locked`: with the claims' lock, while the slot holds `2` every nested call keeps it at `2` and
  only raises fee entries (no claim can run);
* `pot`: with the equalities and either claim defence, every call keeps
  `S.bal + Σ S'.protocolFees ≤ S'.bal + Σ S.protocolFees`. A send's own effect is
  `+msg.value - forwards - burn` on the balance and `+fee` on the ledger, which cancel by the
  equality; a claim's own effect is `-amount` on both; nested calls add their own non-negative
  changes. Without the write first, the claim's final zeroing removes at least the amount, by
  `locked`;
* `zk`: under the standard-token premise, `zkBalance - Σ zkFees` never drops (no ZK transfer
  calls other code).

`agree`: with the sends' lock (and the claims' lock for a claim), a call with no nested calls is
exactly the `FeeState` transaction; this moves flat runs into the nested model.
-/

namespace Contracts.InteropCenter.FeeState.Reentry

open Contracts.InteropCenter (Word Address CallStarter totalBurnedCallsValue)

/-! ## Sums -/

private theorem sum_update_add' (f : Address → ℕ) (i : Address) (v : ℕ) :
    (∑ a : Address, Function.update f i v a) + f i = (∑ a : Address, f a) + v := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i) f v, Finset.sdiff_singleton_eq_erase]
  have he := Finset.sum_erase_add (Finset.univ : Finset Address) f (Finset.mem_univ i)
  omega

private theorem le_sum' (f : Address → ℕ) (i : Address) : f i ≤ ∑ a : Address, f a :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

private theorem sum_mono' {f g : Address → ℕ} (h : ∀ a, f a ≤ g a) :
    (∑ a : Address, f a) ≤ ∑ a : Address, g a :=
  Finset.sum_le_sum fun a _ => h a

/-! ## The non-recursive pieces -/

theorem enterLock_eq {on : Bool} {S S0 : State} (h : enterLock on S = some S0) :
    (on = true ∧ S.lock = 1 ∧ S0 = { S with lock := 2 }) ∨ (on = false ∧ S0 = S) := by
  unfold enterLock at h
  cases on with
  | true =>
    simp only [ite_true] at h
    split_ifs at h with h1
    cases h
    exact Or.inl ⟨rfl, h1, rfl⟩
  | false =>
    simp only [Bool.false_eq_true, ite_false, Option.some.injEq] at h
    exact Or.inr ⟨rfl, h.symm⟩

theorem exitLock_bal (on : Bool) (S : State) : (exitLock on S).bal = S.bal := by
  cases on <;> rfl

theorem exitLock_fees (on : Bool) (S : State) :
    (exitLock on S).protocolFees = S.protocolFees := by
  cases on <;> rfl

theorem forwardPlain_eq : ∀ (l : List CallStarter) (S S' : State), forwardPlain l S = some S' →
    indirectTotal l ≤ S.bal ∧ S' = { S with bal := S.bal - indirectTotal l }
  | [], S, S', h => by
    simp only [forwardPlain, Option.some.injEq] at h
    subst h
    exact ⟨Nat.zero_le _, by simp [indirectTotal]⟩
  | cs :: rest, S, S', h => by
    simp only [forwardPlain] at h
    by_cases hi : cs.callAttributes.indirectCall = true
    · simp only [hi, ite_true] at h
      split_ifs at h with hv
      obtain ⟨h1, rfl⟩ := forwardPlain_eq rest _ _ h
      have ht : indirectTotal (cs :: rest) =
          cs.callAttributes.indirectCallMessageValue + indirectTotal rest := by
        simp [indirectTotal, hi]
      dsimp only at h1 ⊢
      rw [ht]
      refine ⟨by omega, ?_⟩
      congr 1
      omega
    · simp only [hi, Bool.false_eq_true, ite_false] at h
      obtain ⟨h1, rfl⟩ := forwardPlain_eq rest _ _ h
      have ht : indirectTotal (cs :: rest) = indirectTotal rest := by
        simp [indirectTotal, hi]
      rw [ht]
      exact ⟨h1, rfl⟩

theorem zkFeeStep_eq {P : Params} {S S' : State} {inp : SendInput} (h : zkFeeStep P S inp = some S') :
    (fixedFeePath S inp = true →
      zkTokenFor S inp.zkResolved ≠ 0 ∧
      (P.tokenCode (zkTokenFor S inp.zkResolved)).hasTransfer = true ∧ inp.sender ≠ P.center ∧
      S' = { S with
        zkToken := zkTokenFor S inp.zkResolved
        tokBal := Function.update S.tokBal (zkTokenFor S inp.zkResolved)
          (S.tokBal (zkTokenFor S inp.zkResolved) +
            (P.tokenCode (zkTokenFor S inp.zkResolved)).credited (zkFeeOf S inp))
        zkFees := Function.update S.zkFees inp.coinbase (S.zkFees inp.coinbase + zkFeeOf S inp) }) ∧
    (fixedFeePath S inp = false → S' = S) := by
  unfold zkFeeStep at h
  by_cases hf : fixedFeePath S inp = true
  · simp only [hf, ite_true] at h
    split_ifs at h with hg
    cases h
    exact ⟨fun _ => ⟨hg.1, hg.2.1, hg.2.2, rfl⟩, fun hf' => absurd hf (by simp [hf'])⟩
  · have hf' : fixedFeePath S inp = false := by simpa using hf
    simp only [hf', Bool.false_eq_true, ite_false, Option.some.injEq] at h
    exact ⟨fun ht => absurd ht hf, fun _ => h.symm⟩

theorem zkFeeStep_frame {P : Params} {S S' : State} {inp : SendInput}
    (h : zkFeeStep P S inp = some S') :
    S'.bal = S.bal ∧ S'.protocolFees = S.protocolFees ∧ S'.lock = S.lock ∧
      S'.interopProtocolFee = S.interopProtocolFee ∧ S'.l1ChainId = S.l1ChainId ∧
      S'.zkInteropFee = S.zkInteropFee := by
  have := zkFeeStep_eq h
  cases hf : fixedFeePath S inp with
  | true => obtain ⟨_, _, _, rfl⟩ := this.1 hf; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | false => rw [this.2 hf]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem burnStep_eq {inp : SendInput} {S S' : State} (h : burnStep inp S = some S') :
    totalBurnedCallsValue inp.starters ≤ S.bal ∧
      S' = { S with bal := S.bal - totalBurnedCallsValue inp.starters } := by
  unfold burnStep at h
  split_ifs at h with hb
  cases h
  exact ⟨hb, rfl⟩

theorem finishSend_eq {G : Guards} {inp : SendInput} {pf : ℕ} {rec : SendRecord} {S S' : State}
    (h : finishSend G inp pf rec S = some S') :
    (inp.dest ≠ S.l1ChainId → S.feeUnits + inp.calls < UInt256.size) ∧
    S' = exitLock G.sendLock { S with
      protocolFees := Function.update S.protocolFees inp.coinbase (S.protocolFees inp.coinbase + pf)
      feeUnits := if inp.dest = S.l1ChainId then S.feeUnits else S.feeUnits + inp.calls
      leaves := if inp.dest = S.l1ChainId then S.leaves else S.leaves ++ [inp.calls]
      log := S.log ++ [rec] } := by
  unfold finishSend at h
  split at h
  · rename_i hu
    cases h
    exact ⟨hu, rfl⟩
  · exact absurd h (by simp)

/-- The steps of a successful send. -/
theorem execN_send_view {G : Guards} {K : Checks} {P : Params} {inp : SendInput} {cbs : Cbs}
    {dcb : NRun} {S S' : State} (h : execN G K P (.send inp cbs dcb) S = some S') :
    ∃ S0 S2 S3 S4, enterLock G.sendLock S = some S0 ∧ sendStatic P S0 inp ∧
      buildN G K P cbs inp.starters { S0 with bal := S0.bal + inp.msgValue } = some S2 ∧
      zkFeeStep P S2 inp = some S3 ∧
      (K.valueCheck = true → inp.msgValue = expectedValue P S3 inp) ∧
      (if totalBurnedCallsValue inp.starters = 0 then some S3
        else if sameBase P inp = true then burnStep inp S3 else execRun G K P dcb S3) = some S4 ∧
      finishSend G inp (protocolFeeOf S3 inp) (sendRecord P S3 inp) S4 = some S' := by
  simp only [execN] at h
  split at h
  · exact absurd h (by simp)
  rename_i S0 h0
  split at h
  · rename_i hs
    split at h
    · exact absurd h (by simp)
    rename_i S2 h2
    split at h
    · exact absurd h (by simp)
    rename_i S3 h3
    split at h
    · rename_i hv
      split at h
      · exact absurd h (by simp)
      rename_i S4 h4
      exact ⟨S0, S2, S3, S4, h0, hs, h2, h3, hv, h4, h⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The steps of a successful `claimProtocolFees`. -/
theorem execN_claim_view {G : Guards} {K : Checks} {P : Params} {c r : Address} {cb : NRun}
    {S S' : State} (h : execN G K P (.claimProtocolFees c r cb) S = some S') :
    ∃ S0, enterLock G.claimLock S = some S0 ∧
      ((S0.protocolFees c = 0 ∧ S' = exitLock G.claimLock S0) ∨
       (S0.protocolFees c ≠ 0 ∧ S0.protocolFees c ≤ S0.bal ∧ r ≠ P.center ∧
        ∃ S3, execRun G K P cb
            { S0 with
              protocolFees := if G.writeFirst = true then Function.update S0.protocolFees c 0
                else S0.protocolFees
              bal := S0.bal - S0.protocolFees c
              claims := S0.claims ++ [⟨false, c, r, S0.protocolFees c⟩] } = some S3 ∧
          S' = exitLock G.claimLock
            (if G.writeFirst = true then S3
              else { S3 with protocolFees := Function.update S3.protocolFees c 0 }))) := by
  simp only [execN] at h
  split at h
  · exact absurd h (by simp)
  rename_i S0 h0
  refine ⟨S0, h0, ?_⟩
  split at h
  · rename_i hz
    cases h
    exact Or.inl ⟨hz, rfl⟩
  · rename_i hz
    split at h
    · rename_i hg
      split at h
      · exact absurd h (by simp)
      rename_i S3 h3
      cases h
      exact Or.inr ⟨hz, hg.1, hg.2, S3, h3, rfl⟩
    · exact absurd h (by simp)

theorem execRun_cons_view {G : Guards} {K : Checks} {P : Params} {t : NTx} {rest : NRun}
    {S S' : State} (h : execRun G K P (.cons t rest) S = some S') :
    ∃ S1, execN G K P t S = some S1 ∧ execRun G K P rest S1 = some S' := by
  simp only [execRun] at h
  split at h
  · exact absurd h (by simp)
  rename_i S1 h1
  exact ⟨S1, h1, h⟩

theorem buildN_cons_view {G : Guards} {K : Checks} {P : Params} {r : NRun} {rest : Cbs}
    {cs : CallStarter} {css : List CallStarter} {S S' : State}
    (h : buildN G K P (.cons r rest) (cs :: css) S = some S') :
    (cs.callAttributes.indirectCall = true ∧ cs.callAttributes.indirectCallMessageValue ≤ S.bal ∧
      ∃ S1, execRun G K P r { S with bal := S.bal - cs.callAttributes.indirectCallMessageValue } =
        some S1 ∧ buildN G K P rest css S1 = some S') ∨
    (cs.callAttributes.indirectCall = false ∧ buildN G K P rest css S = some S') := by
  simp only [buildN] at h
  by_cases hi : cs.callAttributes.indirectCall = true
  · simp only [hi, ite_true] at h
    split_ifs at h with hv
    split at h
    · exact absurd h (by simp)
    rename_i S1 h1
    exact Or.inl ⟨hi, hv, S1, h1, h⟩
  · have hi' : cs.callAttributes.indirectCall = false := by simpa using hi
    simp only [hi', Bool.false_eq_true, ite_false] at h
    exact Or.inr ⟨hi', h⟩

/-- A transaction of `FeeState` other than a send or claim leaves the protocol-fee ledger. -/
theorem exec_other_fees {K : Checks} {P : Params} {tx : Tx} {S S' : State}
    (hsc : tx.isSendOrClaim = false) (h : exec K P tx S = some S') :
    S'.protocolFees = S.protocolFees := by
  cases tx with
  | send inp => simp [Tx.isSendOrClaim] at hsc
  | claimProtocolFees c r => simp [Tx.isSendOrClaim] at hsc
  | claimZKFees c r z => simp [Tx.isSendOrClaim] at hsc
  | preview c => simp [exec] at h
  | nativeInflow x =>
    simp only [exec, Option.some.injEq] at h; subst h; rfl
  | tokenInflow t x =>
    simp only [exec, Option.some.injEq] at h; subst h; rfl
  | _ =>
    simp only [exec, initL2Step] at h
    split_ifs at h <;> cases h <;> rfl

private theorem le_update_plus (f : Address → ℕ) (i : Address) (v : ℕ) (c : Address) :
    f c ≤ Function.update f i (f i + v) c := by
  by_cases hc : c = i
  · subst hc; simp
  · simp [Function.update_of_ne hc]

/-! ## `locked`: with the claims' lock held, nested calls only raise fee entries -/

mutual
theorem execN_locked {G : Guards} {K : Checks} {P : Params} (hG : G.claimLock = true) :
    ∀ (t : NTx) (S S' : State), S.lock = 2 → execN G K P t S = some S' →
      S'.lock = 2 ∧ ∀ c, S.protocolFees c ≤ S'.protocolFees c
  | .send inp cbs dcb, S, S', hl, h => by
    obtain ⟨S0, S2, S3, S4, h0, _, h2, h3, _, h4, h5⟩ := execN_send_view h
    rcases enterLock_eq h0 with ⟨_, h1, _⟩ | ⟨hsl, rfl⟩
    · omega
    · obtain ⟨l2, m2⟩ :=
        buildN_locked hG cbs inp.starters { S0 with bal := S0.bal + inp.msgValue } S2 hl h2
      obtain ⟨_, f3, l3, _⟩ := zkFeeStep_frame h3
      have h34 : S4.lock = 2 ∧ ∀ c, S3.protocolFees c ≤ S4.protocolFees c := by
        split at h4
        · cases h4; exact ⟨by rw [l3, l2], fun _ => le_refl _⟩
        · split at h4
          · obtain ⟨_, rfl⟩ := burnStep_eq h4
            exact ⟨by simp only; rw [l3, l2], fun _ => le_refl _⟩
          · exact execRun_locked hG dcb S3 S4 (by rw [l3, l2]) h4
      obtain ⟨l4, m4⟩ := h34
      obtain ⟨_, rfl⟩ := finishSend_eq h5
      rw [hsl]
      refine ⟨by simp only [exitLock, Bool.false_eq_true, ite_false]; exact l4, fun c => ?_⟩
      simp only [exitLock, Bool.false_eq_true, ite_false]
      have := m2 c
      have := m4 c
      have := le_update_plus S4.protocolFees inp.coinbase (protocolFeeOf S3 inp) c
      simp only at *
      rw [f3] at *
      omega
  | .claimProtocolFees c r cb, S, S', hl, h => by
    obtain ⟨S0, h0, _⟩ := execN_claim_view h
    rw [hG] at h0
    rcases enterLock_eq h0 with ⟨_, h1, _⟩ | ⟨h1, _⟩
    · omega
    · exact absurd h1 (by simp)
  | .claimZKFees c r z, S, S', hl, h => by
    simp only [execN, hG, enterLock, ite_true, hl] at h
    exact absurd h (by simp)
  | .other tx, S, S', hl, h => by
    simp only [execN] at h
    split at h
    · exact absurd h (by simp)
    rename_i hsc
    have hsc' : tx.isSendOrClaim = false := by simpa using hsc
    refine ⟨?_, fun c => by rw [exec_other_fees hsc' h]⟩
    cases hi : tx.isInitL2 with
    | true => have := (lock_of_initL2 h hi).1; omega
    | false => rw [lock_preserved h hi, hl]
theorem execRun_locked {G : Guards} {K : Checks} {P : Params} (hG : G.claimLock = true) :
    ∀ (r : NRun) (S S' : State), S.lock = 2 → execRun G K P r S = some S' →
      S'.lock = 2 ∧ ∀ c, S.protocolFees c ≤ S'.protocolFees c
  | .nil, S, S', hl, h => by
    simp only [execRun, Option.some.injEq] at h
    subst h
    exact ⟨hl, fun _ => le_refl _⟩
  | .cons t rest, S, S', hl, h => by
    obtain ⟨S1, h1, h2⟩ := execRun_cons_view h
    obtain ⟨l1, m1⟩ := execN_locked hG t S S1 hl h1
    obtain ⟨l2, m2⟩ := execRun_locked hG rest S1 S' l1 h2
    exact ⟨l2, fun c => le_trans (m1 c) (m2 c)⟩
theorem buildN_locked {G : Guards} {K : Checks} {P : Params} (hG : G.claimLock = true) :
    ∀ (cbs : Cbs) (l : List CallStarter) (S S' : State), S.lock = 2 →
      buildN G K P cbs l S = some S' → S'.lock = 2 ∧ ∀ c, S.protocolFees c ≤ S'.protocolFees c
  | .nil, l, S, S', hl, h => by
    simp only [buildN] at h
    obtain ⟨_, rfl⟩ := forwardPlain_eq l S S' h
    exact ⟨hl, fun _ => le_refl _⟩
  | .cons r rest, [], S, S', hl, h => by
    simp only [buildN, Option.some.injEq] at h
    subst h
    exact ⟨hl, fun _ => le_refl _⟩
  | .cons r rest, cs :: css, S, S', hl, h => by
    rcases buildN_cons_view h with ⟨_, _, S1, h1, h2⟩ | ⟨_, h2⟩
    · obtain ⟨l1, m1⟩ := execRun_locked hG r
        { S with bal := S.bal - cs.callAttributes.indirectCallMessageValue } S1 hl h1
      obtain ⟨l2, m2⟩ := buildN_locked hG rest css S1 S' l1 h2
      exact ⟨l2, fun c => le_trans (m1 c) (m2 c)⟩
    · exact buildN_locked hG rest css S S' hl h2
end

/-! ## `pot`: the native backing never shrinks -/

theorem claimZKFeesBody_frame {P : Params} {S S' : State} {c r z : Address}
    (h : claimZKFeesBody P S c r z = some S') :
    S'.bal = S.bal ∧ S'.protocolFees = S.protocolFees := by
  unfold claimZKFeesBody at h
  split_ifs at h <;> cases h <;> exact ⟨rfl, rfl⟩

private theorem enterLock_frame {on : Bool} {S S0 : State} (h : enterLock on S = some S0) :
    S0.bal = S.bal ∧ S0.protocolFees = S.protocolFees := by
  rcases enterLock_eq h with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> exact ⟨rfl, rfl⟩

/-- `expectedValue` as indirect total, burned total (same base token only) and fee. -/
private theorem expectedValue_eq (P : Params) (S : State) (inp : SendInput) :
    expectedValue P S inp = indirectTotal inp.starters +
      (if sameBase P inp = true then totalBurnedCallsValue inp.starters else 0) +
      protocolFeeOf S inp := by
  unfold expectedValue
  split_ifs <;> omega

mutual
theorem execN_pot {G : Guards} {K : Checks} {P : Params} (hK : K.valueCheck = true)
    (hG : G.writeFirst = true ∨ G.claimLock = true) :
    ∀ (t : NTx) (S S' : State), execN G K P t S = some S' →
      S.bal + (∑ c : Address, S'.protocolFees c) ≤ S'.bal + (∑ c : Address, S.protocolFees c)
  | .send inp cbs dcb, S, S', h => by
    obtain ⟨S0, S2, S3, S4, h0, _, h2, h3, hv, h4, h5⟩ := execN_send_view h
    obtain ⟨b0, f0⟩ := enterLock_frame h0
    have ih2 := buildN_pot hK hG cbs inp.starters { S0 with bal := S0.bal + inp.msgValue } S2 h2
    simp only [b0, f0] at ih2
    obtain ⟨b3, f3, _, _, _, _⟩ := zkFeeStep_frame h3
    have e3 : (∑ x : Address, S3.protocolFees x) = ∑ x : Address, S2.protocolFees x := by rw [f3]
    have hv' := hv hK
    rw [expectedValue_eq] at hv'
    obtain ⟨_, rfl⟩ := finishSend_eq h5
    rw [exitLock_bal, exitLock_fees]
    simp only
    split at h4
    · rename_i hb0
      cases h4
      rw [hb0] at hv'
      simp only [ite_self, add_zero] at hv'
      have hs := sum_update_add' S3.protocolFees inp.coinbase
        (S3.protocolFees inp.coinbase + protocolFeeOf S3 inp)
      omega
    · split at h4
      · rename_i hsb
        obtain ⟨hle, rfl⟩ := burnStep_eq h4
        rw [hsb] at hv'
        simp only [ite_true] at hv'
        have hs := sum_update_add' S3.protocolFees inp.coinbase
          (S3.protocolFees inp.coinbase + protocolFeeOf S3 inp)
        simp only
        omega
      · rename_i hsb
        have ih4 := execRun_pot hK hG dcb S3 S4 h4
        simp only [hsb, Bool.false_eq_true, ite_false, add_zero] at hv'
        have hs := sum_update_add' S4.protocolFees inp.coinbase
          (S4.protocolFees inp.coinbase + protocolFeeOf S3 inp)
        omega
  | .claimProtocolFees c r cb, S, S', h => by
    obtain ⟨S0, h0, hcase⟩ := execN_claim_view h
    obtain ⟨b0, f0⟩ := enterLock_frame h0
    rcases hcase with ⟨_, rfl⟩ | ⟨hz, hle, _, S3, h3, rfl⟩
    · rw [exitLock_bal, exitLock_fees, b0, f0]
    · have ih := execRun_pot hK hG cb _ S3 h3
      have hsum : S.protocolFees c ≤ ∑ x : Address, S.protocolFees x := le_sum' _ c
      rw [b0, f0] at hle
      rw [exitLock_bal, exitLock_fees]
      cases hw : G.writeFirst with
      | true =>
        have hz0 := sum_update_add' S.protocolFees c 0
        simp only [hw, ite_true, b0, f0] at ih ⊢
        omega
      | false =>
        have hcl : G.claimLock = true := by
          rcases hG with hG | hG
          · rw [hw] at hG; exact absurd hG (by simp)
          · exact hG
        rcases enterLock_eq h0 with ⟨_, _, hS0⟩ | ⟨hon, _⟩
        · have hlk := (execRun_locked hcl cb _ S3 (by rw [hS0]) h3).2 c
          have hz3 := sum_update_add' S3.protocolFees c 0
          have hs3 := le_sum' S3.protocolFees c
          simp only [hw, Bool.false_eq_true, ite_false, b0, f0] at ih hlk ⊢
          omega
        · rw [hcl] at hon; exact absurd hon (by simp)
  | .claimZKFees c r z, S, S', h => by
    simp only [execN] at h
    split at h
    · exact absurd h (by simp)
    rename_i S0 h0
    obtain ⟨b0, f0⟩ := enterLock_frame h0
    cases hb : claimZKFeesBody P S0 c r z with
    | none => rw [hb] at h; exact absurd h (by simp)
    | some S1 =>
      rw [hb] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨b1, f1⟩ := claimZKFeesBody_frame hb
      rw [exitLock_bal, exitLock_fees, b1, f1, b0, f0]
  | .other tx, S, S', h => by
    simp only [execN] at h
    split at h
    · exact absurd h (by simp)
    have h1 := native_step hK h
    have h2 := forcedIn_mono h
    omega
theorem execRun_pot {G : Guards} {K : Checks} {P : Params} (hK : K.valueCheck = true)
    (hG : G.writeFirst = true ∨ G.claimLock = true) :
    ∀ (r : NRun) (S S' : State), execRun G K P r S = some S' →
      S.bal + (∑ c : Address, S'.protocolFees c) ≤ S'.bal + (∑ c : Address, S.protocolFees c)
  | .nil, S, S', h => by
    simp only [execRun, Option.some.injEq] at h
    subst h
    exact le_refl _
  | .cons t rest, S, S', h => by
    obtain ⟨S1, h1, h2⟩ := execRun_cons_view h
    have := execN_pot hK hG t S S1 h1
    have := execRun_pot hK hG rest S1 S' h2
    omega
theorem buildN_pot {G : Guards} {K : Checks} {P : Params} (hK : K.valueCheck = true)
    (hG : G.writeFirst = true ∨ G.claimLock = true) :
    ∀ (cbs : Cbs) (l : List CallStarter) (S S' : State), buildN G K P cbs l S = some S' →
      S.bal + (∑ c : Address, S'.protocolFees c) ≤
        S'.bal + (∑ c : Address, S.protocolFees c) + indirectTotal l
  | .nil, l, S, S', h => by
    simp only [buildN] at h
    obtain ⟨hle, rfl⟩ := forwardPlain_eq l S S' h
    simp only
    omega
  | .cons r rest, [], S, S', h => by
    simp only [buildN, Option.some.injEq] at h
    subst h
    omega
  | .cons r rest, cs :: css, S, S', h => by
    rcases buildN_cons_view h with ⟨hi, hv, S1, h1, h2⟩ | ⟨hi, h2⟩
    · have ih1 := execRun_pot hK hG r
        { S with bal := S.bal - cs.callAttributes.indirectCallMessageValue } S1 h1
      have ih2 := buildN_pot hK hG rest css S1 S' h2
      have ht : indirectTotal (cs :: css) =
          cs.callAttributes.indirectCallMessageValue + indirectTotal css := by
        simp [indirectTotal, hi]
      simp only at ih1
      rw [ht]
      omega
    · have ih2 := buildN_pot hK hG rest css S S' h2
      have ht : indirectTotal (cs :: css) = indirectTotal css := by
        simp [indirectTotal, hi]
      rw [ht]
      exact ih2
end

/-! ## `zk`: the ZK backing never shrinks -/

/-- `zkBalance - Σ zkFees` does not drop from `S` to `S'`. -/
def ZkLE (S S' : State) : Prop :=
  zkBalance S + (∑ c : Address, S'.zkFees c) ≤ zkBalance S' + (∑ c : Address, S.zkFees c)

theorem ZkLE.trans {a b c : State} (h1 : ZkLE a b) (h2 : ZkLE b c) : ZkLE a c := by
  unfold ZkLE at *
  omega

theorem ZkLE.of_frame {S S' : State} (h1 : S'.zkToken = S.zkToken) (h2 : S'.tokBal = S.tokBal)
    (h3 : S'.zkFees = S.zkFees) : ZkLE S S' := by
  unfold ZkLE zkBalance
  rw [h1, h2, h3]

theorem ZkLE.exitLock (on : Bool) (S : State) : ZkLE S (exitLock on S) := by
  cases on <;> exact ZkLE.of_frame rfl rfl rfl

theorem ZkLE.enterLock {on : Bool} {S S0 : State} (h : enterLock on S = some S0) : ZkLE S S0 := by
  rcases enterLock_eq h with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> exact ZkLE.of_frame rfl rfl rfl

private theorem zkBalance_set (S : State) (t : Address) (g f : Address → ℕ) (ht : t ≠ 0) :
    zkBalance { S with zkToken := t, tokBal := g, zkFees := f } = g t := by
  simp [zkBalance, ht]

theorem zkFeeStep_zk {P : Params} {S S' : State} {inp : SendInput} (hP : StandardTokens P)
    (h : zkFeeStep P S inp = some S') : ZkLE S S' := by
  have he := zkFeeStep_eq h
  cases hf : fixedFeePath S inp with
  | false => rw [he.2 hf]; exact ZkLE.of_frame rfl rfl rfl
  | true =>
    obtain ⟨ht0, htr, _, rfl⟩ := he.1 hf
    have hstd : P.tokenCode (zkTokenFor S inp.zkResolved) = .standard := by
      cases hc : P.tokenCode (zkTokenFor S inp.zkResolved) with
      | standard => rfl
      | noTransfer => rw [hc] at htr; simp [TokenCode.hasTransfer] at htr
      | nonStandard f => exact absurd hc (hP _ f)
    have hs := sum_update_add' S.zkFees inp.coinbase (S.zkFees inp.coinbase + zkFeeOf S inp)
    have hle := zkBalance_le (zkTokenFor_cases S inp.zkResolved)
    unfold ZkLE
    rw [zkBalance_set _ _ _ _ ht0, Function.update_self, hstd]
    simp only [TokenCode.credited]
    omega

theorem claimZKFeesBody_zk {P : Params} {S S' : State} {c r z : Address}
    (h : claimZKFeesBody P S c r z = some S') : ZkLE S S' := by
  unfold claimZKFeesBody at h
  split_ifs at h with h2 h3 hr
  · cases h; exact ZkLE.of_frame rfl rfl rfl
  · cases h
    obtain ⟨ht0, _, hcov⟩ := h3
    have hz := sum_update_add' S.zkFees c 0
    have hle := zkBalance_le (zkTokenFor_cases S z)
    unfold ZkLE
    have hb : zkBalance { S with
        zkFees := Function.update S.zkFees c 0
        zkToken := zkTokenFor S z
        tokBal := S.tokBal
        claims := S.claims ++ [⟨true, c, r, S.zkFees c⟩] } = S.tokBal (zkTokenFor S z) := by
      simp [zkBalance, ht0]
    rw [hb]
    dsimp only
    omega
  · cases h
    obtain ⟨ht0, _, hcov⟩ := h3
    have hz := sum_update_add' S.zkFees c 0
    have hle := zkBalance_le (zkTokenFor_cases S z)
    unfold ZkLE
    have hb : zkBalance { S with
        zkFees := Function.update S.zkFees c 0
        zkToken := zkTokenFor S z
        tokBal := Function.update S.tokBal (zkTokenFor S z) (S.tokBal (zkTokenFor S z) - S.zkFees c)
        claims := S.claims ++ [⟨true, c, r, S.zkFees c⟩] } =
          S.tokBal (zkTokenFor S z) - S.zkFees c := by
      simp [zkBalance, ht0]
    rw [hb]
    dsimp only
    omega

mutual
theorem execN_zk {G : Guards} {K : Checks} {P : Params} (hP : StandardTokens P) :
    ∀ (t : NTx) (S S' : State), execN G K P t S = some S' → ZkLE S S'
  | .send inp cbs dcb, S, S', h => by
    obtain ⟨S0, S2, S3, S4, h0, _, h2, h3, _, h4, h5⟩ := execN_send_view h
    have z0 := ZkLE.enterLock h0
    have z1 : ZkLE S0 { S0 with bal := S0.bal + inp.msgValue } := ZkLE.of_frame rfl rfl rfl
    have z2 := buildN_zk hP cbs inp.starters _ S2 h2
    have z3 := zkFeeStep_zk hP h3
    have z4 : ZkLE S3 S4 := by
      split at h4
      · cases h4; exact ZkLE.of_frame rfl rfl rfl
      · split at h4
        · obtain ⟨_, rfl⟩ := burnStep_eq h4; exact ZkLE.of_frame rfl rfl rfl
        · exact execRun_zk hP dcb S3 S4 h4
    obtain ⟨_, rfl⟩ := finishSend_eq h5
    have z5 : ZkLE S4 { S4 with
        protocolFees := Function.update S4.protocolFees inp.coinbase
          (S4.protocolFees inp.coinbase + protocolFeeOf S3 inp)
        feeUnits := if inp.dest = S4.l1ChainId then S4.feeUnits else S4.feeUnits + inp.calls
        leaves := if inp.dest = S4.l1ChainId then S4.leaves else S4.leaves ++ [inp.calls]
        log := S4.log ++ [sendRecord P S3 inp] } := ZkLE.of_frame rfl rfl rfl
    exact ((((z0.trans z1).trans z2).trans z3).trans z4).trans (z5.trans (ZkLE.exitLock _ _))
  | .claimProtocolFees c r cb, S, S', h => by
    obtain ⟨S0, h0, hcase⟩ := execN_claim_view h
    have z0 := ZkLE.enterLock h0
    rcases hcase with ⟨_, rfl⟩ | ⟨_, _, _, S3, h3, rfl⟩
    · exact z0.trans (ZkLE.exitLock _ _)
    · have z1 := execRun_zk hP cb _ S3 h3
      have z2 : ZkLE S3 (if G.writeFirst = true then S3
          else { S3 with protocolFees := Function.update S3.protocolFees c 0 }) := by
        split_ifs <;> exact ZkLE.of_frame rfl rfl rfl
      exact ((z0.trans (ZkLE.of_frame rfl rfl rfl)).trans z1).trans (z2.trans (ZkLE.exitLock _ _))
  | .claimZKFees c r z, S, S', h => by
    simp only [execN] at h
    split at h
    · exact absurd h (by simp)
    rename_i S0 h0
    cases hb : claimZKFeesBody P S0 c r z with
    | none => rw [hb] at h; exact absurd h (by simp)
    | some S1 =>
      rw [hb] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact ((ZkLE.enterLock h0).trans (claimZKFeesBody_zk hb)).trans (ZkLE.exitLock _ _)
  | .other tx, S, S', h => by
    simp only [execN] at h
    split at h
    · exact absurd h (by simp)
    exact zk_step hP h
theorem execRun_zk {G : Guards} {K : Checks} {P : Params} (hP : StandardTokens P) :
    ∀ (r : NRun) (S S' : State), execRun G K P r S = some S' → ZkLE S S'
  | .nil, S, S', h => by
    simp only [execRun, Option.some.injEq] at h
    subst h
    exact ZkLE.of_frame rfl rfl rfl
  | .cons t rest, S, S', h => by
    obtain ⟨S1, h1, h2⟩ := execRun_cons_view h
    exact (execN_zk hP t S S1 h1).trans (execRun_zk hP rest S1 S' h2)
theorem buildN_zk {G : Guards} {K : Checks} {P : Params} (hP : StandardTokens P) :
    ∀ (cbs : Cbs) (l : List CallStarter) (S S' : State), buildN G K P cbs l S = some S' →
      ZkLE S S'
  | .nil, l, S, S', h => by
    simp only [buildN] at h
    obtain ⟨_, rfl⟩ := forwardPlain_eq l S S' h
    exact ZkLE.of_frame rfl rfl rfl
  | .cons r rest, [], S, S', h => by
    simp only [buildN, Option.some.injEq] at h
    subst h
    exact ZkLE.of_frame rfl rfl rfl
  | .cons r rest, cs :: css, S, S', h => by
    rcases buildN_cons_view h with ⟨_, _, S1, h1, h2⟩ | ⟨_, h2⟩
    · have z1 : ZkLE S { S with bal := S.bal - cs.callAttributes.indirectCallMessageValue } :=
        ZkLE.of_frame rfl rfl rfl
      exact (z1.trans (execRun_zk hP r _ S1 h1)).trans (buildN_zk hP rest css S1 S' h2)
    · exact buildN_zk hP rest css S S' h2
end

/-! ## `agree`: a call with no nested calls is the `FeeState` transaction -/

theorem forwardPlain_complete : ∀ (l : List CallStarter) (S : State), indirectTotal l ≤ S.bal →
    forwardPlain l S = some { S with bal := S.bal - indirectTotal l }
  | [], S, _ => by simp [forwardPlain, indirectTotal]
  | cs :: rest, S, h => by
    simp only [forwardPlain]
    by_cases hi : cs.callAttributes.indirectCall = true
    · have ht : indirectTotal (cs :: rest) =
          cs.callAttributes.indirectCallMessageValue + indirectTotal rest := by
        simp [indirectTotal, hi]
      rw [ht] at h ⊢
      rw [ite_eq_left hi, ite_eq_left (by omega),
        forwardPlain_complete rest _ (by dsimp only; omega)]
      congr 2
      dsimp only
      omega
    · have ht : indirectTotal (cs :: rest) = indirectTotal rest := by
        simp [indirectTotal, hi]
      rw [ht] at h ⊢
      rw [ite_eq_right hi]
      exact forwardPlain_complete rest S h


theorem execN_send_complete {G : Guards} {K : Checks} {P : Params} {S : State} {inp : SendInput}
    (hsl : G.sendLock = true) (hok : SendOk K P S inp) :
    execN G K P (.send inp .nil .nil) S = some (afterSend P S inp) := by
  obtain ⟨hlock, hl1, hself, htoL1, hind, hfund, hval, hzk, hunits⟩ := hok
  rw [nativeOut_sendPayments] at hfund
  have hs : sendStatic P { S with lock := 2 } inp := ⟨hl1, hself, htoL1, hind⟩
  have hiT : indirectTotal inp.starters ≤ S.bal + inp.msgValue := by
    split_ifs at hfund <;> omega
  simp only [execN, hsl, enterLock, ite_true, hlock]
  rw [ite_eq_left hs]
  simp only [buildN]
  rw [forwardPlain_complete _ _ (by dsimp only; omega)]
  dsimp only
  simp only [zkFeeStep, burnStep, finishSend, exitLock, execRun, afterSend, sendRecord,
    nativeOut_sendPayments]
  simp only [fixedFeePath, zkTokenFor, zkFeeOf, protocolFeeOf, expectedValue, sameBase] at hzk hval hunits hfund ⊢
  by_cases hb0 : totalBurnedCallsValue inp.starters = 0
  · simp only [hb0, ite_true] at hfund hval ⊢
    split_ifs <;> simp_all
  · by_cases hsb : inp.destBase = P.baseAssetId
    · simp only [hb0, hsb, ite_false] at hval ⊢
      simp [hsb] at hfund
      have hburn : totalBurnedCallsValue inp.starters ≤
          S.bal + inp.msgValue - indirectTotal inp.starters := by omega
      split_ifs <;> (try simp only []) <;> (try rw [ite_eq_left hburn]) <;> simp_all <;> omega
    · simp only [hb0, hsb, ite_false] at hfund hval ⊢
      split_ifs <;> simp_all

private theorem expectedValue_congr {P : Params} {S T : State} {inp : SendInput}
    (h1 : S.interopProtocolFee = T.interopProtocolFee) (h2 : S.l1ChainId = T.l1ChainId) :
    expectedValue P S inp = expectedValue P T inp := by
  simp only [expectedValue, protocolFeeOf, h1, h2]

/-- A send that runs with no nested calls is one `FeeState` accepts. -/
theorem execN_send_sound {G : Guards} {K : Checks} {P : Params} {S S' : State} {inp : SendInput}
    (hsl : G.sendLock = true) (h : execN G K P (.send inp .nil .nil) S = some S') :
    SendOk K P S inp := by
  obtain ⟨S0, S2, S3, S4, h0, hs, h2, h3, hv, h4, h5⟩ := execN_send_view h
  rw [hsl] at h0
  rcases enterLock_eq h0 with ⟨_, hlock, rfl⟩ | ⟨hf, _⟩
  swap
  · exact absurd hf (by simp)
  obtain ⟨hl1, hself, htoL1, hind⟩ := hs
  simp only [buildN] at h2
  obtain ⟨hiT, rfl⟩ := forwardPlain_eq _ _ _ h2
  have e3 := zkFeeStep_eq h3
  obtain ⟨b3, _, _, i3, c3, _⟩ := zkFeeStep_frame h3
  have u3 : S3.feeUnits = S.feeUnits := by
    unfold zkFeeStep at h3
    split_ifs at h3 <;> cases h3 <;> rfl
  obtain ⟨hu, rfl⟩ := finishSend_eq h5
  have h4' : S4.feeUnits = S3.feeUnits ∧ S4.l1ChainId = S3.l1ChainId ∧
      (totalBurnedCallsValue inp.starters ≠ 0 → sameBase P inp = true →
        totalBurnedCallsValue inp.starters ≤ S3.bal) := by
    split at h4
    · cases h4; exact ⟨rfl, rfl, fun h => absurd ‹_› h⟩
    · split at h4
      · obtain ⟨hle, rfl⟩ := burnStep_eq h4; exact ⟨rfl, rfl, fun _ _ => hle⟩
      · simp only [execRun, Option.some.injEq] at h4
        subst h4
        rename_i hsb
        exact ⟨rfl, rfl, fun _ h => absurd h hsb⟩
  obtain ⟨u4, l4, hb4⟩ := h4'
  refine ⟨hlock, hl1, hself, htoL1, hind, ?_, fun hK => ?_, fun hf => ?_, ?_⟩
  · rw [nativeOut_sendPayments]
    simp only at hiT b3
    by_cases hb0 : totalBurnedCallsValue inp.starters = 0
    · split_ifs <;> omega
    · by_cases hsb : sameBase P inp = true
      · have := hb4 hb0 hsb
        rw [ite_eq_left hsb]
        omega
      · rw [ite_eq_right hsb]; omega
  · rw [hv hK]
    exact expectedValue_congr i3 c3
  · have := (e3.1 hf)
    exact ⟨this.1, this.2.1, this.2.2.1⟩
  · intro hd
    have := hu (by rw [l4, c3]; exact hd)
    rw [u4, u3] at this
    exact this

/-- **AGREEMENT FOR SENDS.** With the sends' lock, a send with no nested calls is the `FeeState`
send. -/
theorem execN_send_nil {G : Guards} {K : Checks} {P : Params} {S : State} {inp : SendInput}
    (hsl : G.sendLock = true) : execN G K P (.send inp .nil .nil) S = exec K P (.send inp) S := by
  by_cases hok : SendOk K P S inp
  · rw [execN_send_complete hsl hok]
    simp only [exec, hok, ite_true]
  · simp only [exec, hok, ite_false]
    cases h : execN G K P (.send inp .nil .nil) S with
    | none => rfl
    | some S' => exact absurd (execN_send_sound hsl h) hok

/-- **AGREEMENT FOR `claimProtocolFees`.** With the claims' lock, a claim whose receiver makes no
call is the `FeeState` claim, whatever the order of write and call. -/
theorem execN_claimP_nil {G : Guards} {K : Checks} {P : Params} {S : State} {c r : Address}
    (hcl : G.claimLock = true) :
    execN G K P (.claimProtocolFees c r .nil) S = exec K P (.claimProtocolFees c r) S := by
  obtain ⟨bal, tokBal, pf, zf, ipf, zif, zid, l1, zk, lock, pa, ow, po, fu, fi, lv, lg, cl⟩ := S
  simp only [execN, exec, claimProtocolFeesStep, enterLock, hcl, ite_true, exitLock, execRun]
  by_cases hl : lock = 1
  · subst hl
    simp only [ite_true]
    split_ifs <;> simp_all
  · simp [hl]

/-- **AGREEMENT FOR `claimZKFees`.** With the claims' lock, the claim is the `FeeState` claim. -/
theorem execN_claimZ_nil {G : Guards} {K : Checks} {P : Params} {S : State} {c r z : Address}
    (hcl : G.claimLock = true) :
    execN G K P (.claimZKFees c r z) S = exec K P (.claimZKFees c r z) S := by
  obtain ⟨bal, tokBal, pf, zf, ipf, zif, zid, l1, zk, lock, pa, ow, po, fu, fi, lv, lg, cl⟩ := S
  simp only [execN, exec, claimZKFeesStep, claimZKFeesBody, enterLock, hcl, ite_true,
    zkTokenFor]
  by_cases hl : lock = 1
  · subst hl
    simp only [ite_true]
    split_ifs <;> simp_all [exitLock]
  · simp [hl]

/-- **AGREEMENT.** With the sends' lock, and the claims' lock if `tx` is a claim, the `FeeState`
transaction `tx` is the call `liftTx tx` with no nested calls. -/
theorem execN_liftTx {G : Guards} {K : Checks} {P : Params} {S : State} {tx : Tx}
    (hsl : G.sendLock = true) (hcl : tx.isClaim = true → G.claimLock = true) :
    execN G K P (liftTx tx) S = exec K P tx S := by
  cases tx with
  | send inp => exact execN_send_nil hsl
  | claimProtocolFees c r => exact execN_claimP_nil (hcl rfl)
  | claimZKFees c r z => exact execN_claimZ_nil (hcl rfl)
  | _ => simp [liftTx, execN, Tx.isSendOrClaim]

theorem runN_liftTx {G : Guards} {K : Checks} {P : Params} (hsl : G.sendLock = true) :
    ∀ (txs : List Tx) (S S' : State), (∀ tx ∈ txs, tx.isClaim = true → G.claimLock = true) →
      run K P txs S = some S' → runN G K P (txs.map liftTx) S = some S'
  | [], S, S', _, h => h
  | tx :: rest, S, S', hcl, h => by
    simp only [run] at h
    simp only [List.map_cons, runN]
    rw [execN_liftTx hsl (hcl tx (List.mem_cons_self ..))]
    cases hx : exec K P tx S with
    | none => rw [hx] at h; exact absurd h (by simp)
    | some S1 =>
      rw [hx] at h
      exact runN_liftTx hsl rest S1 S' (fun t ht => hcl t (List.mem_cons_of_mem _ ht)) h


/-! ## Runs -/

theorem runN_rel {G : Guards} {K : Checks} {P : Params} (R : State → State → Prop)
    (hrefl : ∀ S, R S S) (htrans : ∀ a b c, R a b → R b c → R a c)
    (hstep : ∀ t S S', execN G K P t S = some S' → R S S') :
    ∀ ts S S', runN G K P ts S = some S' → R S S' := by
  intro ts
  induction ts with
  | nil =>
    intro S S' h
    simp only [runN, Option.some.injEq] at h
    subst h
    exact hrefl S
  | cons t rest ih =>
    intro S S' h
    simp only [runN] at h
    cases hx : execN G K P t S with
    | none => rw [hx] at h; exact absurd h (by simp)
    | some S1 => rw [hx] at h; exact htrans _ _ _ (hstep _ _ _ hx) (ih _ _ h)

theorem runN_snoc {G : Guards} {K : Checks} {P : Params} {t : NTx} :
    ∀ (ts : List NTx) (S S1 S2 : State), runN G K P ts S = some S1 →
      execN G K P t S1 = some S2 → runN G K P (ts ++ [t]) S = some S2
  | [], S, S1, S2, h1, h2 => by
    simp only [runN, Option.some.injEq] at h1
    subst h1
    simp [runN, h2]
  | t' :: rest, S, S1, S2, h1, h2 => by
    simp only [runN] at h1
    cases hx : execN G K P t' S with
    | none => rw [hx] at h1; exact absurd h1 (by simp)
    | some S3 =>
      rw [hx] at h1
      simp only [List.cons_append, runN, hx]
      exact runN_snoc rest S3 S1 S2 h1 h2

/-! ## The properties -/

theorem FlatIsNestedWithoutCalls : Properties.FlatIsNestedWithoutCalls :=
  fun _ _ _ _ _ hsl hcl => execN_liftTx hsl hcl

theorem NestedBackingNeverShrinks : Properties.NestedBackingNeverShrinks := by
  intro G K P hK hG t S S' h
  have := execN_pot hK hG t S S' h
  rw [← Nat.cast_sum, ← Nat.cast_sum]
  omega

theorem NestedProtocolFeesBacked : Properties.NestedProtocolFeesBacked := by
  intro G K P S hK hG ⟨ts, h⟩
  have key := runN_rel (G := G) (K := K) (P := P)
    (fun a b => a.bal + (∑ c : Address, b.protocolFees c) ≤ b.bal + (∑ c : Address, a.protocolFees c))
    (fun _ => le_refl _) (fun a b c hab hbc => by omega)
    (fun t _ _ h => execN_pot hK hG t _ _ h) ts init S h
  simp only [init, Finset.sum_const_zero, zero_add, add_zero] at key
  exact key

theorem NestedZkFeesBacked : Properties.NestedZkFeesBacked := by
  intro G K P S hP ⟨ts, h⟩
  have key := runN_rel (G := G) (K := K) (P := P) ZkLE (fun _ => ZkLE.of_frame rfl rfl rfl)
    (fun _ _ _ h1 h2 => h1.trans h2) (fun t _ _ h => execN_zk hP t _ _ h) ts init S h
  unfold ZkLE at key
  have h0 : zkBalance init = 0 := rfl
  have hs : (∑ c : Address, init.zkFees c) = 0 := by simp [init]
  rw [h0, hs] at key
  refine ⟨fun hz c => ?_, by omega⟩
  have hb : zkBalance S = 0 := by simp [zkBalance, hz]
  have := le_sum' S.zkFees c
  omega

theorem HeldLockBlocksSendsAndClaims : Properties.HeldLockBlocksSendsAndClaims := by
  intro K P S hl
  refine ⟨fun inp cbs dcb => ?_, fun c r cb => ?_, fun c r z => ?_⟩ <;>
    simp [execN, deployedGuards, enterLock, hl]

/-- The setup has no claim. -/
private theorem wSetupTxs_noClaim (G : Guards) :
    ∀ tx ∈ wSetupTxs, tx.isClaim = true → G.claimLock = true := by
  intro tx htx hc
  simp only [wSetupTxs, List.mem_cons, List.not_mem_nil, or_false] at htx
  rcases htx with rfl | rfl | rfl | rfl <;> simp [Tx.isClaim, wInit, wSetFee] at hc

set_option maxHeartbeats 800000 in
theorem NoLockNoWriteFirstDrainsFees : Properties.NoLockNoWriteFirstDrainsFees := by
  obtain ⟨S, hS, hbal, h77, h78, hdep, ⟨S1, h1, hb1⟩, S2, h2, hb2, h278⟩ :
      ∃ S, run deployed wP wSetupTxs init = some S ∧ S.bal = 12 ∧ S.protocolFees 0x77 = 6 ∧
        S.protocolFees 0x78 = 6 ∧ execN deployedGuards deployed wP wReenteringClaim S = none ∧
        (∃ S1, execN withoutClaimLock deployed wP wReenteringClaim S = some S1 ∧ S1.bal = 6) ∧
        ∃ S2, execN withoutClaimLockPayFirst deployed wP wReenteringClaim S = some S2 ∧
          S2.bal = 0 ∧ S2.protocolFees 0x78 = 6 :=
    ⟨_, rfl, by decide, by decide, by decide, rfl, ⟨_, rfl, by decide⟩, ⟨_, rfl, by decide, by decide⟩⟩
  refine ⟨S, S1, S2, ⟨_, runN_liftTx rfl _ _ _ (wSetupTxs_noClaim _) hS⟩,
    ⟨_, runN_liftTx rfl _ _ _ (wSetupTxs_noClaim _) hS⟩,
    ⟨_, runN_liftTx rfl _ _ _ (wSetupTxs_noClaim _) hS⟩, hbal, h77, h78, hdep, h1, hb1, h2, hb2, ?_⟩
  rw [hb2]
  exact lt_of_lt_of_le (by rw [h278]; decide) (le_sum' _ 0x78)

set_option maxHeartbeats 800000 in
theorem NestedClaimInsideSendWitness : Properties.NestedClaimInsideSendWitness := by
  obtain ⟨S, hS, h77, hdep, S', h', hcl, hp, hb⟩ :
      ∃ S, run deployed wP [wInit, wSetFee, .send wSendA] init = some S ∧
        S.protocolFees 0x77 = 6 ∧ execN deployedGuards deployed wP wSendWithNestedClaim S = none ∧
        ∃ S', execN withoutClaimLock deployed wP wSendWithNestedClaim S = some S' ∧
          S'.claims.length = 1 ∧ S'.protocolFees 0x77 = 6 ∧ S'.bal = 6 :=
    ⟨_, rfl, by decide, rfl, ⟨_, rfl, by decide⟩⟩
  have hnc : ∀ (G : Guards), ∀ tx ∈ [wInit, wSetFee, .send wSendA],
      tx.isClaim = true → G.claimLock = true := by
    intro G tx htx hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htx
    rcases htx with rfl | rfl | rfl <;> simp [Tx.isClaim, wInit, wSetFee] at hc
  have hR := runN_liftTx (G := withoutClaimLock) rfl _ _ _ (hnc _) hS
  exact ⟨S, S', ⟨_, runN_liftTx rfl _ _ _ (hnc _) hS⟩, ⟨_, hR⟩, h77, hdep, h', hcl, hp, hb,
    ⟨_, runN_snoc _ _ _ _ hR h'⟩⟩

set_option maxHeartbeats 800000 in
theorem PayFirstClaimLockNestedWitness : Properties.PayFirstClaimLockNestedWitness := by
  refine ⟨?_, ?_⟩
  · obtain ⟨S, hS, h77, hb, S1, h1, hp1, hb1, hf1, hc1, hblk⟩ :
        ∃ S, run deployed wP [wInit, wSetFee, .send wSendA] init = some S ∧
          S.protocolFees 0x77 = 6 ∧ S.bal = 6 ∧
          ∃ S1, execN payFirst deployed wP wClaimWithNestedInflow S = some S1 ∧
            S1.protocolFees 0x77 = 0 ∧ S1.bal = 1 ∧ S1.forcedIn = 1 ∧ S1.claims.length = 1 ∧
            execN payFirst deployed wP wClaimWithNestedSend S = none :=
      ⟨_, rfl, by decide, by decide, ⟨_, rfl, by decide, by decide, by decide, by decide, rfl⟩⟩
    have hnc : ∀ tx ∈ [wInit, wSetFee, .send wSendA], tx.isClaim = true → payFirst.claimLock = true :=
      fun _ _ _ => rfl
    have hR := runN_liftTx (G := payFirst) rfl _ _ _ hnc hS
    exact ⟨S, S1, ⟨_, hR⟩, h77, hb, h1, hp1, hb1, hf1, hc1, ⟨_, runN_snoc _ _ _ _ hR h1⟩, hblk⟩
  · -- The setup state is computed by the flat run; that the nested run without the sends' lock
    -- reaches the same state is checked by evaluation (`runN_liftTx` needs the sends' lock).
    obtain ⟨S, -, hSN, h77, hb, S2, h2, hlog, hp2, hb2, hc2⟩ :
        ∃ S, run deployed wP [wInit, wSetFee, .send wSendA] init = some S ∧
          runN withoutSendLockPayFirst deployed wP ([wInit, wSetFee, .send wSendA].map liftTx)
            init = some S ∧
          S.protocolFees 0x77 = 6 ∧ S.bal = 6 ∧
          ∃ S2, execN withoutSendLockPayFirst deployed wP wClaimWithNestedSend S = some S2 ∧
            S2.log.map (fun r => (r.input.coinbase, r.protocolFee)) = [(0x77, 6), (0x77, 6)] ∧
            S2.protocolFees 0x77 = 0 ∧ S2.bal = 6 ∧ S2.claims.length = 1 :=
      ⟨_, rfl, rfl, by decide, by decide, ⟨_, rfl, by decide, by decide, by decide, by decide⟩⟩
    exact ⟨S, S2, ⟨_, hSN⟩, h77, hb, h2, hlog, hp2, hb2, hc2, ⟨_, runN_snoc _ _ _ _ hSN h2⟩⟩

end Contracts.InteropCenter.FeeState.Reentry
