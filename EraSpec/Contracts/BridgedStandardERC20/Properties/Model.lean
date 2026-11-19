import EraSpec.Contracts.BridgedStandardERC20.Specs.Model
import EraSpec.Core.Headline

-- Preconditions are retained as statement parameters for the full-proof audit.
set_option linter.unusedVariables false

/-! Reviewable ledger and authority statements for the initialized-vault slice. The exact effect
and success condition of `transfer` are in `Properties/ModelStrong.lean`.

Classification (`EraSpec.Core.Headline`): `balance_bounded`, `unauthorized_bridge_calls`,
`burn_exact`, `mint_exact` and `reachable_ledger` are `@[headline]`s; `one_unit_roundtrip` is their
`@[witness]`. The rest are supporting lemmas. -/

namespace Contracts.BridgedStandardERC20

/-- **NO BALANCE EXCEEDS THE SUPPLY, AND BOTH FIT A uint256.** Premise: the ledger is `WellFormed`
(the balances of all `2^160` addresses sum to the total supply, the supply is below `2^256`, and the
zero address holds nothing), which every ledger reachable from a well-formed one is
(`reachable_ledger`). Then every account's balance is at most the total supply and below `2^256`. -/
@[headline] abbrev Properties.balance_bounded {s : State} (h : WellFormed s) (a : Address) :=
  s.balances a ≤ s.totalSupply ∧ s.balances a < UInt256.size

/-- **ONLY THE CONFIGURED VAULT CAN BRIDGE-MINT OR BRIDGE-BURN.** Premise: the caller is not the
vault recorded in the token's configuration. Then `bridgeBurn` and `bridgeMint` revert, for every
account and amount. The model is the nonzero-vault branch of `onlyNTV`; the zero-vault (legacy)
branch is `Properties/LegacyFallback.lean`. -/
@[headline] abbrev Properties.unauthorized_bridge_calls {s : State} {caller account : Address}
    {amount : UInt256} (h : caller ≠ s.config.vault) :=
  burn s caller account amount = none ∧ mint s caller account amount = none

/-- **A BURN REMOVES EXACTLY THE AMOUNT FROM ONE BALANCE AND FROM THE SUPPLY.** Premises: the ledger
is `WellFormed`, and `bridgeBurn` of `amount` from `owner` succeeded. Then the caller was the
configured vault, which is nonzero; `owner`'s balance and the total supply each fell by exactly
`amount`; every other balance and the vault, origin token and asset id are unchanged. No allowance
is required. -/
@[headline] abbrev Properties.burn_exact {s t : State} {caller owner : Address} {amount : UInt256}
    (hw : WellFormed s) (h : burn s caller owner amount = some t) :=
  caller = s.config.vault ∧ s.config.vault ≠ 0 ∧
  t.balances owner + amount.val = s.balances owner ∧
  t.totalSupply + amount.val = s.totalSupply ∧
  (∀ other, other ≠ owner → t.balances other = s.balances other) ∧
  t.config = s.config

abbrev Properties.burn_preserves_ledger {s t : State} {caller owner : Address}
    {amount : UInt256} (hw : WellFormed s)
    (h : burn s caller owner amount = some t) := WellFormed t

/-- **A MINT ADDS EXACTLY THE AMOUNT TO ONE BALANCE AND TO THE SUPPLY.** Premise: `bridgeMint` of
`amount` to `recipient` succeeded (no ledger premise). Then the caller was the configured vault,
which is nonzero; `recipient`'s balance and the total supply each rose by exactly `amount`; every
other balance and the vault, origin token and asset id are unchanged. -/
@[headline] abbrev Properties.mint_exact {s t : State} {caller recipient : Address} {amount : UInt256}
    (h : mint s caller recipient amount = some t) :=
  caller = s.config.vault ∧ s.config.vault ≠ 0 ∧
  t.balances recipient = s.balances recipient + amount.val ∧
  t.totalSupply = s.totalSupply + amount.val ∧
  (∀ other, other ≠ recipient → t.balances other = s.balances other) ∧
  t.config = s.config

abbrev Properties.mint_preserves_ledger {s t : State} {caller recipient : Address}
    {amount : UInt256} (hw : WellFormed s)
    (h : mint s caller recipient amount = some t) := WellFormed t

/-- Ordinary spending preserves total supply and all ledger bounds. This does not say which
balances move: a transfer that moved nothing, or credited another account, would satisfy it too.
The exact effect is `Properties.transfer_exact` and `Properties.transfer_balances_exact`, and when a
transfer succeeds is `Properties.transfer_succeeds_iff` (`Properties/ModelStrong.lean`). -/
abbrev Properties.transfer_preserves_ledger {s t : State} {owner recipient : Address}
    {amount : UInt256} (hw : WellFormed s)
    (h : transfer s owner recipient amount = some t) :=
  WellFormed t ∧ t.totalSupply = s.totalSupply ∧ t.config = s.config

/-- A successful self-transfer has no token-ledger effect, including at zero. -/
abbrev Properties.self_transfer_identity {s t : State} {account : Address}
    {amount : UInt256} (h : transfer s account account amount = some t) := t = s

/-- **THE LEDGER STAYS CONSISTENT ACROSS EVERY SEQUENCE OF CALLS.** Premises: the starting ledger is
`WellFormed`, and some finite sequence of successful mints, burns and transfers, by any callers in
any order, leads from it to `t` (`Reach`). Then `t` is `WellFormed` (balances sum to the supply, the
supply fits a uint256, the zero address holds nothing) and has the same vault, origin token and
asset id. -/
@[headline] abbrev Properties.reachable_ledger {s t : State}
    (hw : WellFormed s) (h : Reach s t) := WellFormed t ∧ t.config = s.config

abbrev Properties.insufficient_burn_rejected {s : State} {caller owner : Address}
    {amount : UInt256} (h : s.balances owner < amount.val) :=
  burn s caller owner amount = none

abbrev Properties.overflowing_mint_rejected {s : State} {caller recipient : Address}
    {amount : UInt256} (h : UInt256.size ≤ s.totalSupply + amount.val) :=
  mint s caller recipient amount = none

/-- **Witness** for the headlines above. For any configuration with a nonzero vault and any nonzero
account: the empty ledger is `WellFormed`, the vault's one-unit mint to the account succeeds to a
`WellFormed` ledger, and the vault's one-unit burn from it returns exactly the empty ledger. So the
premises of `burn_exact`, `mint_exact` and `reachable_ledger` are met by real calls. -/
@[witness] abbrev Properties.one_unit_roundtrip (config : Config) (account : Address)
    (hv : config.vault ≠ 0) (ha : account ≠ 0) :=
  WellFormed (empty config) ∧
  ∃ funded, mint (empty config) config.vault account 1 = some funded ∧
    WellFormed funded ∧ burn funded config.vault account 1 = some (empty config)

end Contracts.BridgedStandardERC20
