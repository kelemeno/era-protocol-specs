import EraSpec.Contracts.BridgedStandardERC20.Specs.Model

-- Preconditions are retained as statement parameters for the full-proof audit.
set_option linter.unusedVariables false

/-! Reviewable ledger and authority statements for the initialized-vault slice. -/

namespace Contracts.BridgedStandardERC20

/-- Each balance is backed by total supply, which fits a uint256. -/
abbrev Properties.balance_bounded {s : State} (h : WellFormed s) (a : Address) :=
  s.balances a ≤ s.totalSupply ∧ s.balances a < UInt256.size

/-- The configured vault is the sole bridge mint/burn authority in this slice. -/
abbrev Properties.unauthorized_bridge_calls {s : State} {caller account : Address}
    {amount : UInt256} (h : caller ≠ s.config.vault) :=
  burn s caller account amount = none ∧ mint s caller account amount = none

/-- Burn removes exactly the input from one balance and supply; all other
balances and the asset/vault identity stay unchanged. No allowance is required. -/
abbrev Properties.burn_exact {s t : State} {caller owner : Address} {amount : UInt256}
    (hw : WellFormed s) (h : burn s caller owner amount = some t) :=
  caller = s.config.vault ∧ s.config.vault ≠ 0 ∧
  t.balances owner + amount.val = s.balances owner ∧
  t.totalSupply + amount.val = s.totalSupply ∧
  (∀ other, other ≠ owner → t.balances other = s.balances other) ∧
  t.config = s.config

abbrev Properties.burn_preserves_ledger {s t : State} {caller owner : Address}
    {amount : UInt256} (hw : WellFormed s)
    (h : burn s caller owner amount = some t) := WellFormed t

abbrev Properties.mint_exact {s t : State} {caller recipient : Address} {amount : UInt256}
    (h : mint s caller recipient amount = some t) :=
  caller = s.config.vault ∧ s.config.vault ≠ 0 ∧
  t.balances recipient = s.balances recipient + amount.val ∧
  t.totalSupply = s.totalSupply + amount.val ∧
  (∀ other, other ≠ recipient → t.balances other = s.balances other) ∧
  t.config = s.config

abbrev Properties.mint_preserves_ledger {s t : State} {caller recipient : Address}
    {amount : UInt256} (hw : WellFormed s)
    (h : mint s caller recipient amount = some t) := WellFormed t

/-- Ordinary spending preserves total supply and all ledger bounds. -/
abbrev Properties.transfer_preserves_ledger {s t : State} {owner recipient : Address}
    {amount : UInt256} (hw : WellFormed s)
    (h : transfer s owner recipient amount = some t) :=
  WellFormed t ∧ t.totalSupply = s.totalSupply ∧ t.config = s.config

/-- A successful self-transfer has no token-ledger effect, including at zero. -/
abbrev Properties.self_transfer_identity {s t : State} {account : Address}
    {amount : UInt256} (h : transfer s account account amount = some t) := t = s

/-- Inductive accounting over arbitrary interleavings, not just one example. -/
abbrev Properties.reachable_ledger {s t : State}
    (hw : WellFormed s) (h : Reach s t) := WellFormed t ∧ t.config = s.config

abbrev Properties.insufficient_burn_rejected {s : State} {caller owner : Address}
    {amount : UInt256} (h : s.balances owner < amount.val) :=
  burn s caller owner amount = none

abbrev Properties.overflowing_mint_rejected {s : State} {caller recipient : Address}
    {amount : UInt256} (h : UInt256.size ≤ s.totalSupply + amount.val) :=
  mint s caller recipient amount = none

/-- Non-vacuity: a valid one-unit mint followed by a one-unit burn exists.
The final ledger is exactly the original empty ledger. -/
abbrev Properties.one_unit_roundtrip (config : Config) (account : Address)
    (hv : config.vault ≠ 0) (ha : account ≠ 0) :=
  WellFormed (empty config) ∧
  ∃ funded, mint (empty config) config.vault account 1 = some funded ∧
    WellFormed funded ∧ burn funded config.vault account 1 = some (empty config)

end Contracts.BridgedStandardERC20
