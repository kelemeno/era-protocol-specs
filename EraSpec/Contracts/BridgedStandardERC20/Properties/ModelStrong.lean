import EraSpec.Contracts.BridgedStandardERC20.Specs.Model

-- Preconditions are retained as statement parameters for the full-proof audit.
set_option linter.unusedVariables false

/-!
# Properties: the exact effect of `transfer`

Statements about `EraSpec.Contracts.BridgedStandardERC20.Specs.Model`. Proofs are in
`EraSpec.Contracts.BridgedStandardERC20.Proofs.ModelStrong`.

`Properties/Model.lean` gives `burn` and `mint` exact-effect statements (`burn_exact`,
`mint_exact`), but for `transfer` it states only that the ledger invariant, the supply and the
configuration are kept (`transfer_preserves_ledger`) and that a self-transfer is the identity
(`self_transfer_identity`). Those two conclusions also hold for a transfer that accepts and moves
nothing, and for one that credits the wrong account. This file adds what they leave out:

* **When a transfer succeeds** (`transfer_succeeds_iff`): exactly when the owner and the recipient
  are nonzero and the owner holds the amount. So the model's transfer does not always revert, and
  an overdraft or a transfer from or to the zero address always reverts.
* **What it does** (`transfer_exact`): between two distinct accounts, the owner loses exactly the
  amount, the recipient gains exactly the amount, and every other balance, the total supply and the
  configuration are unchanged. `transfer_balances_exact` is the same effect as one equation per
  account, and covers self-transfers too.
* **Non-vacuity** (`transfer_moves_value_witness`): after the vault's one-unit mint to `a`, a
  one-unit transfer from `a` to a distinct nonzero `b` succeeds and changes the ledger, and the
  vault can then burn the unit from `b`, back to the empty ledger.
-/

namespace Contracts.BridgedStandardERC20

/-- **WHEN A TRANSFER SUCCEEDS.** Exactly when the owner and the recipient are nonzero and the
owner's balance covers the amount (`TransferAllowed`, OpenZeppelin `_transfer`'s two zero-address
checks and its balance check). The model has no other guard: no caller, vault or supply
condition. -/
abbrev Properties.transfer_succeeds_iff (s : State) (owner recipient : Address)
    (amount : UInt256) :=
  (∃ t, transfer s owner recipient amount = some t) ↔
    owner ≠ 0 ∧ recipient ≠ 0 ∧ amount.val ≤ s.balances owner

/-- **A TRANSFER BETWEEN TWO ACCOUNTS MOVES EXACTLY THE AMOUNT.** After a successful transfer
from `owner` to a different `recipient`: both were nonzero, the owner's balance fell by exactly
the amount, the recipient's rose by exactly the amount, every other balance is unchanged, and so
are the total supply and the vault, origin token and asset id. No ledger premise. -/
abbrev Properties.transfer_exact {s t : State} {owner recipient : Address} {amount : UInt256}
    (hne : owner ≠ recipient) (h : transfer s owner recipient amount = some t) :=
  owner ≠ 0 ∧ recipient ≠ 0 ∧
  t.balances owner + amount.val = s.balances owner ∧
  t.balances recipient = s.balances recipient + amount.val ∧
  (∀ other, other ≠ owner → other ≠ recipient → t.balances other = s.balances other) ∧
  t.totalSupply = s.totalSupply ∧ t.config = s.config

/-- **THE SAME EFFECT, ONE EQUATION PER ACCOUNT, SELF-TRANSFERS INCLUDED.** After a successful
transfer, every account's new balance plus the amount it sent (the amount for the owner, else zero)
equals its old balance plus the amount it received (the amount for the recipient, else zero). For
`owner = recipient` this says every balance is unchanged. -/
abbrev Properties.transfer_balances_exact {s t : State} {owner recipient : Address}
    {amount : UInt256} (h : transfer s owner recipient amount = some t) (a : Address) :=
  t.balances a + (if a = owner then amount.val else 0) =
    s.balances a + (if a = recipient then amount.val else 0)

/-- **A TRANSFER THAT MOVES VALUE.** For any configuration with a nonzero vault and any two
distinct nonzero accounts `a` and `b`: the vault's one-unit mint to `a` on the empty ledger
succeeds; then a one-unit transfer from `a` to `b` succeeds, to a `WellFormed` ledger different from
the one before it, in which `a` holds nothing, `b` holds the unit and the supply is one; and the
vault's one-unit burn from `b` then returns exactly the empty ledger. This meets the premises of
`transfer_exact` and `transfer_balances_exact` with a nonzero amount. -/
abbrev Properties.transfer_moves_value_witness (config : Config) (a b : Address)
    (hv : config.vault ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :=
  ∃ funded moved : State,
    mint (empty config) config.vault a 1 = some funded ∧
    transfer funded a b 1 = some moved ∧
    WellFormed moved ∧ moved ≠ funded ∧
    moved.balances a = 0 ∧ moved.balances b = 1 ∧ moved.totalSupply = 1 ∧
    burn moved config.vault b 1 = some (empty config)

end Contracts.BridgedStandardERC20
