import EraSpec.Contracts.BridgedStandardERC20.Properties.ModelStrong
import EraSpec.Contracts.BridgedStandardERC20.Proofs.Model

/-!
# Proofs: the exact effect of `transfer`

`transferEffect` debits the owner and then credits the recipient on the debited map. For distinct
accounts the two `Function.update`s touch different keys; for a self-transfer the credit undoes the
debit, which is exact because the guard gives `amount ≤ balance`.
-/

namespace Contracts.BridgedStandardERC20

/-- A successful transfer, unfolded to its guard and its effect. -/
private theorem transferStrong_view {s t : State} {owner recipient : Address}
    {amount : UInt256} (h : transfer s owner recipient amount = some t) :
    TransferAllowed s owner recipient amount ∧ t = transferEffect s owner recipient amount := by
  unfold transfer at h
  split at h
  · rename_i hg
    exact ⟨hg, (Option.some.inj h).symm⟩
  · cases h

private theorem transferStrong_of_allowed {s : State} {owner recipient : Address}
    {amount : UInt256} (h : TransferAllowed s owner recipient amount) :
    transfer s owner recipient amount = some (transferEffect s owner recipient amount) := by
  unfold transfer
  exact ite_eq_left h

theorem transfer_succeeds_iff (s : State) (owner recipient : Address) (amount : UInt256) :
    Properties.transfer_succeeds_iff s owner recipient amount := by
  unfold Properties.transfer_succeeds_iff
  constructor
  · rintro ⟨t, h⟩
    exact (transferStrong_view h).1
  · intro h
    exact ⟨_, transferStrong_of_allowed h⟩

theorem transfer_exact {s t : State} {owner recipient : Address} {amount : UInt256}
    (hne : owner ≠ recipient) (h : transfer s owner recipient amount = some t) :
    Properties.transfer_exact hne h := by
  unfold Properties.transfer_exact
  obtain ⟨⟨ho, hr, hb⟩, rfl⟩ := transferStrong_view h
  refine ⟨ho, hr, ?_, ?_, ?_, rfl, rfl⟩
  · change Function.update (Function.update s.balances owner (s.balances owner - amount.val))
        recipient (Function.update s.balances owner (s.balances owner - amount.val) recipient +
          amount.val) owner + amount.val = s.balances owner
    rw [Function.update_of_ne hne, Function.update_self]
    exact Nat.sub_add_cancel hb
  · change Function.update (Function.update s.balances owner (s.balances owner - amount.val))
        recipient (Function.update s.balances owner (s.balances owner - amount.val) recipient +
          amount.val) recipient = s.balances recipient + amount.val
    rw [Function.update_self, Function.update_of_ne (Ne.symm hne)]
  · intro other hother_o hother_r
    change Function.update (Function.update s.balances owner (s.balances owner - amount.val))
        recipient (Function.update s.balances owner (s.balances owner - amount.val) recipient +
          amount.val) other = s.balances other
    rw [Function.update_of_ne hother_r, Function.update_of_ne hother_o]

theorem transfer_balances_exact {s t : State} {owner recipient : Address}
    {amount : UInt256} (h : transfer s owner recipient amount = some t) (a : Address) :
    Properties.transfer_balances_exact h a := by
  unfold Properties.transfer_balances_exact
  obtain ⟨⟨_, _, hb⟩, rfl⟩ := transferStrong_view h
  change Function.update (Function.update s.balances owner (s.balances owner - amount.val))
      recipient (Function.update s.balances owner (s.balances owner - amount.val) recipient +
        amount.val) a + (if a = owner then amount.val else 0) =
    s.balances a + (if a = recipient then amount.val else 0)
  by_cases har : a = recipient
  · subst har
    rw [Function.update_self, ite_eq_left rfl]
    by_cases hao : a = owner
    · subst hao
      rw [Function.update_self, ite_eq_left rfl]
      omega
    · rw [Function.update_of_ne hao, ite_eq_right hao]
      omega
  · rw [Function.update_of_ne har, ite_eq_right har]
    by_cases hao : a = owner
    · subst hao
      rw [Function.update_self, ite_eq_left rfl]
      omega
    · rw [Function.update_of_ne hao, ite_eq_right hao]

theorem transfer_moves_value_witness (config : Config) (a b : Address)
    (hv : config.vault ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    Properties.transfer_moves_value_witness config a b hv ha hb hab := by
  unfold Properties.transfer_moves_value_witness
  have h1 : (1 : UInt256).val = 1 := rfl
  obtain ⟨hw0, funded, hmint, hwf, _⟩ := one_unit_roundtrip config a hv ha
  -- the minted ledger: `a` holds the unit, nobody else holds anything
  have hfunded : funded = ⟨config, Function.update (fun _ => 0) a 1, 1⟩ := by
    have hm : mint (empty config) config.vault a 1 =
        some (mintEffect (empty config) a 1) := by
      unfold mint
      exact ite_eq_left (by norm_num [MintAllowed, empty, hv, ha, UInt256.size])
    rw [hm] at hmint
    rw [← Option.some.inj hmint]
    simp only [mintEffect, empty, h1, Nat.zero_add]
  subst hfunded
  have hta : TransferAllowed ⟨config, Function.update (fun _ => 0) a 1, 1⟩ a b 1 := by
    refine ⟨ha, hb, ?_⟩
    show (1 : UInt256).val ≤ Function.update (fun _ => 0) a 1 a
    rw [Function.update_self, h1]
  have htr := transferStrong_of_allowed hta
  -- the moved ledger: `b` holds the unit, nobody else holds anything
  have hmoved : transferEffect ⟨config, Function.update (fun _ => 0) a 1, 1⟩ a b 1 =
      ⟨config, Function.update (fun _ => 0) b 1, 1⟩ := by
    simp only [transferEffect, Function.update_self, Function.update_idem, h1, Nat.sub_self,
      Function.update_of_ne (Ne.symm hab), Nat.zero_add]
    congr 1
    have hz : Function.update (fun _ : Address => (0 : ℕ)) a 0 = fun _ => 0 :=
      Function.update_eq_self a (fun _ : Address => (0 : ℕ))
    rw [hz]
  rw [hmoved] at htr
  have hwm : WellFormed ⟨config, Function.update (fun _ => 0) b 1, 1⟩ := by
    rw [← hmoved]
    rw [← hmoved] at htr
    exact (transfer_preserves_ledger hwf htr).1
  refine ⟨_, _, hmint, htr, hwm, ?_, ?_, ?_, rfl, ?_⟩
  · intro heq
    have hbal := congrArg (fun s : State => s.balances b) heq
    simp only [Function.update_self, Function.update_of_ne (Ne.symm hab)] at hbal
    exact absurd hbal (by decide)
  · show Function.update (fun _ => 0) b 1 a = 0
    rw [Function.update_of_ne hab]
  · show Function.update (fun _ => 0) b 1 b = 1
    rw [Function.update_self]
  · have hba : BurnAllowed ⟨config, Function.update (fun _ => 0) b 1, 1⟩ config.vault b 1 := by
      refine ⟨hv, rfl, hb, ?_⟩
      show (1 : UInt256).val ≤ Function.update (fun _ => 0) b 1 b
      rw [Function.update_self, h1]
    unfold burn
    rw [ite_eq_left hba]
    congr 1
    simp only [burnEffect, empty, Function.update_self, Function.update_idem, h1, Nat.sub_self]
    congr 1
    exact Function.update_eq_self b (fun _ : Address => (0 : ℕ))

end Contracts.BridgedStandardERC20
