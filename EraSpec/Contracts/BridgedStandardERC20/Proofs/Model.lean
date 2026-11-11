import EraSpec.Contracts.BridgedStandardERC20.Properties.Model

namespace Contracts.BridgedStandardERC20

private theorem sum_update_add (f : Address → ℕ) (i : Address) (v : ℕ) :
    (∑ a : Address, Function.update f i v a) + f i = (∑ a : Address, f a) + v := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i) f v,
    Finset.sdiff_singleton_eq_erase]
  have he := Finset.sum_erase_add (Finset.univ : Finset Address) f (Finset.mem_univ i)
  omega

private theorem balance_le_supply {s : State} (h : WellFormed s) (a : Address) :
    s.balances a ≤ s.totalSupply := by
  rw [← h.1]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

private theorem burn_view {s t : State} {caller owner : Address} {amount : UInt256}
    (h : burn s caller owner amount = some t) :
    BurnAllowed s caller owner amount ∧ t = burnEffect s owner amount := by
  simp only [burn, Option.ite_none_right_eq_some, Option.some.injEq] at h
  exact ⟨h.1, h.2.symm⟩

private theorem mint_view {s t : State} {caller recipient : Address} {amount : UInt256}
    (h : mint s caller recipient amount = some t) :
    MintAllowed s caller recipient amount ∧ t = mintEffect s recipient amount := by
  simp only [mint, Option.ite_none_right_eq_some, Option.some.injEq] at h
  exact ⟨h.1, h.2.symm⟩

private theorem transfer_view {s t : State} {owner recipient : Address} {amount : UInt256}
    (h : transfer s owner recipient amount = some t) :
    TransferAllowed s owner recipient amount ∧ t = transferEffect s owner recipient amount := by
  simp only [transfer, Option.ite_none_right_eq_some, Option.some.injEq] at h
  exact ⟨h.1, h.2.symm⟩

theorem balance_bounded {s : State} (h : WellFormed s) (a : Address) :
    Properties.balance_bounded h a :=
  ⟨balance_le_supply h a, (balance_le_supply h a).trans_lt h.2.1⟩

theorem unauthorized_bridge_calls {s : State} {caller account : Address}
    {amount : UInt256} (h : caller ≠ s.config.vault) :
    Properties.unauthorized_bridge_calls (account := account) (amount := amount) h := by
  simp only [Properties.unauthorized_bridge_calls, burn, mint, BurnAllowed, MintAllowed,
    h, false_and, and_false, ite_false, and_self]

theorem burn_exact {s t : State} {caller owner : Address} {amount : UInt256}
    (hw : WellFormed s) (h : burn s caller owner amount = some t) :
    Properties.burn_exact hw h := by
  obtain ⟨⟨hv, hc, -, hb⟩, rfl⟩ := burn_view h
  refine ⟨hc, hv, ?_, Nat.sub_add_cancel (hb.trans (balance_le_supply hw owner)),
    fun _ ho => Function.update_of_ne ho _ _, rfl⟩
  simpa only [burnEffect, Function.update_self] using Nat.sub_add_cancel hb

theorem burn_preserves_ledger {s t : State} {caller owner : Address}
    {amount : UInt256} (hw : WellFormed s)
    (h : burn s caller owner amount = some t) :
    Properties.burn_preserves_ledger hw h := by
  obtain ⟨⟨-, -, hn, hb⟩, rfl⟩ := burn_view h
  refine ⟨?_, (Nat.sub_le _ _).trans_lt hw.2.1, ?_⟩
  · have hu := sum_update_add s.balances owner (s.balances owner - amount.val)
    have := hw.1
    have := balance_le_supply hw owner
    dsimp only [burnEffect]
    omega
  · simp only [burnEffect, Function.update_of_ne (Ne.symm hn), hw.2.2]

theorem mint_exact {s t : State} {caller recipient : Address} {amount : UInt256}
    (h : mint s caller recipient amount = some t) :
    Properties.mint_exact h := by
  obtain ⟨⟨hv, hc, -, -⟩, rfl⟩ := mint_view h
  exact ⟨hc, hv, Function.update_self _ _ _, rfl, fun _ ho => Function.update_of_ne ho _ _, rfl⟩

theorem mint_preserves_ledger {s t : State} {caller recipient : Address}
    {amount : UInt256} (hw : WellFormed s)
    (h : mint s caller recipient amount = some t) :
    Properties.mint_preserves_ledger hw h := by
  obtain ⟨⟨-, -, hn, hs⟩, rfl⟩ := mint_view h
  refine ⟨?_, hs, ?_⟩
  · have hu := sum_update_add s.balances recipient (s.balances recipient + amount.val)
    have := hw.1
    dsimp only [mintEffect]
    omega
  · simp only [mintEffect, Function.update_of_ne (Ne.symm hn), hw.2.2]

theorem transfer_preserves_ledger {s t : State} {owner recipient : Address}
    {amount : UInt256} (hw : WellFormed s)
    (h : transfer s owner recipient amount = some t) :
    Properties.transfer_preserves_ledger hw h := by
  obtain ⟨⟨ho, hr, hb⟩, rfl⟩ := transfer_view h
  refine ⟨⟨?_, hw.2.1, ?_⟩, rfl, rfl⟩
  · have h₁ := sum_update_add s.balances owner (s.balances owner - amount.val)
    have := hw.1
    dsimp only [transferEffect]
    set debited := Function.update s.balances owner (s.balances owner - amount.val)
    have h₂ := sum_update_add debited recipient (debited recipient + amount.val)
    omega
  · simp only [transferEffect, Function.update_of_ne (Ne.symm hr),
      Function.update_of_ne (Ne.symm ho), hw.2.2]

theorem self_transfer_identity {s t : State} {account : Address}
    {amount : UInt256} (h : transfer s account account amount = some t) :
    Properties.self_transfer_identity h := by
  obtain ⟨ha, rfl⟩ := transfer_view h
  change transferEffect s account account amount = s
  simp only [transferEffect, Function.update_self, Nat.sub_add_cancel ha.2.2,
    Function.update_idem, Function.update_eq_self]

theorem reachable_ledger {s t : State} (hw : WellFormed s) (h : Reach s t) :
    Properties.reachable_ledger hw h := by
  unfold Properties.reachable_ledger
  induction h with
  | refl => exact ⟨hw, rfl⟩
  | tail _hr hs ih =>
    cases hs with
    | burn hb =>
      rcases burn_exact ih.1 hb with ⟨_, _, _, _, _, hc⟩
      exact ⟨burn_preserves_ledger ih.1 hb, hc.trans ih.2⟩
    | mint hm =>
      rcases mint_exact hm with ⟨_, _, _, _, _, hc⟩
      exact ⟨mint_preserves_ledger ih.1 hm, hc.trans ih.2⟩
    | transfer ht =>
      obtain ⟨wf, _, hc⟩ := transfer_preserves_ledger ih.1 ht
      exact ⟨wf, hc.trans ih.2⟩

theorem insufficient_burn_rejected {s : State} {caller owner : Address}
    {amount : UInt256} (h : s.balances owner < amount.val) :
    Properties.insufficient_burn_rejected (caller := caller) h := by
  simp only [Properties.insufficient_burn_rejected, burn, BurnAllowed,
    Nat.not_le_of_gt h, and_false, ite_false]

theorem overflowing_mint_rejected {s : State} {caller recipient : Address}
    {amount : UInt256} (h : UInt256.size ≤ s.totalSupply + amount.val) :
    Properties.overflowing_mint_rejected (caller := caller) (recipient := recipient) h := by
  simp only [Properties.overflowing_mint_rejected, mint, MintAllowed,
    Nat.not_lt_of_ge h, and_false, ite_false]

theorem one_unit_roundtrip (config : Config) (account : Address)
    (hv : config.vault ≠ 0) (ha : account ≠ 0) :
    Properties.one_unit_roundtrip config account hv ha := by
  have hw : WellFormed (empty config) :=
    ⟨Finset.sum_const_zero, by norm_num [empty, UInt256.size], rfl⟩
  have hm : MintAllowed (empty config) config.vault account 1 := by
    norm_num [MintAllowed, empty, hv, ha, UInt256.size]
  have hmint : mint (empty config) config.vault account 1 =
      some (mintEffect (empty config) account 1) := ite_eq_left hm
  refine ⟨hw, mintEffect (empty config) account 1, hmint,
    mint_preserves_ledger hw hmint, ?_⟩
  have hb : BurnAllowed (mintEffect (empty config) account 1) config.vault account 1 := by
    simp [BurnAllowed, mintEffect, empty, hv, ha]
  rw [burn, ite_eq_left hb]
  simp [burnEffect, mintEffect, empty]

end Contracts.BridgedStandardERC20
