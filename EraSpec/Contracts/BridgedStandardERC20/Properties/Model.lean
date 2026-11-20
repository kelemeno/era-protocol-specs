import EraSpec.Contracts.BridgedStandardERC20.Specs.Model
import EraSpec.Core.Headline

-- Preconditions are retained as statement parameters for the full-proof audit.
set_option linter.unusedVariables false

/-! Reviewable ledger and authority statements for the initialized-vault slice. The exact effect
and success condition of `transfer` are in `Properties/ModelStrong.lean`.

**Model boundary.** This model is the nonzero-vault branch of `onlyNTV`
(`BridgedStandardERC20.sol:49-61`): its `mint` and `burn` refuse every bridge call on a token whose
configured vault is zero (`original_model_rejects_legacy`). The deployed token does not: on such a
legacy token the L2 native token vault may mint and burn, and the call first rewrites the vault and
the asset id (`Properties/LegacyFallback.lean`). Read at a zero vault, the bridge-call and run
statements of this file describe the model, not `b17415d20`, so they are supporting lemmas. The
headlines about the deployed calls carry the nonzero-vault premise in their Lean statements and are
in `Properties/LegacyFallback.lean`: `nonlegacy_unauthorized_bridge_calls` (from
`unauthorized_bridge_calls`), `nonlegacy_bridge_mint_exact` (from `mint_exact`),
`nonlegacy_bridge_burn_exact` (from `burn_exact`) and `nonlegacy_reachable_ledger` (from
`reachable_ledger`), with the witness `nonlegacy_one_unit_roundtrip` (from `one_unit_roundtrip`).

Classification (`EraSpec.Core.Headline`): `balance_bounded`, a statement about a ledger state that
does not depend on the vault, is a `@[headline]`. The rest are supporting lemmas. -/

namespace Contracts.BridgedStandardERC20

/-- **NO BALANCE EXCEEDS THE SUPPLY, AND BOTH FIT A uint256.** Premise: the ledger is `WellFormed`
(the balances of all `2^160` addresses sum to the total supply, the supply is below `2^256`, and the
zero address holds nothing), which every ledger the deployed token reaches from a well-formed one
is (`nonlegacy_reachable_ledger`, `legacy_reachable_ledger`). Then every account's balance is at
most the total supply and below `2^256`. -/
@[headline] abbrev Properties.balance_bounded {s : State} (h : WellFormed s) (a : Address) :=
  s.balances a ≤ s.totalSupply ∧ s.balances a < UInt256.size

/-- **Model only.** In the nonlegacy model, a caller that is not the configured vault cannot
`burn` or `mint`, for every account and amount. The model's `mint` and `burn` refuse every call on a
zero vault, which the deployed token does not, so this is not a headline. The headline about the
deployed calls, with the premise that the vault is nonzero, is
`nonlegacy_unauthorized_bridge_calls`; the zero-vault branch is `legacy_unauthorized_bridge_calls`
(both in `Properties/LegacyFallback.lean`). -/
abbrev Properties.unauthorized_bridge_calls {s : State} {caller account : Address}
    {amount : UInt256} (h : caller ≠ s.config.vault) :=
  burn s caller account amount = none ∧ mint s caller account amount = none

/-- **Model only.** If the ledger is `WellFormed` and the model's `burn` of `amount` from `owner`
succeeded, then the caller was the configured vault, which is nonzero; `owner`'s balance and the
total supply each fell by exactly `amount`; every other balance and the vault, origin token and
asset id are unchanged. The conjunct `s.config.vault ≠ 0` holds of the model only: a successful
burn on a deployed legacy token starts from a zero vault and rewrites the configuration
(`legacy_bridge_burn_exact`). The headline about the deployed `bridgeBurn` is
`nonlegacy_bridge_burn_exact` (`Properties/LegacyFallback.lean`). -/
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

/-- **Model only.** If the model's `mint` of `amount` to `recipient` succeeded (no ledger premise),
then the caller was the configured vault, which is nonzero; `recipient`'s balance and the total
supply each rose by exactly `amount`; every other balance and the vault, origin token and asset id
are unchanged. The conjunct `s.config.vault ≠ 0` holds of the model only: a successful mint on a
deployed legacy token starts from a zero vault and rewrites the configuration
(`legacy_bridge_mint_exact`). The headline about the deployed `bridgeMint` is
`nonlegacy_bridge_mint_exact` (`Properties/LegacyFallback.lean`). -/
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

/-- **Model only.** Along every run of the nonlegacy model (`Reach`: successful model mints, burns
and transfers, by any callers in any order) from a `WellFormed` ledger, the ledger stays
`WellFormed` and the vault, origin token and asset id are unchanged. From a legacy token the model
has transfers only, while the deployed runs rewrite the vault and asset id once
(`legacy_run_config`). The headline about the deployed runs is `nonlegacy_reachable_ledger`
(`Properties/LegacyFallback.lean`); `legacy_reachable_ledger` covers the ledger from a legacy token,
and `Properties/ReinitializationStrong.lean` the runs with every modelled entry point
(`DeployedRunsPreserveLedger`, `DeployedInitializedIdentityIsFixed`). -/
abbrev Properties.reachable_ledger {s t : State}
    (hw : WellFormed s) (h : Reach s t) := WellFormed t ∧ t.config = s.config

abbrev Properties.insufficient_burn_rejected {s : State} {caller owner : Address}
    {amount : UInt256} (h : s.balances owner < amount.val) :=
  burn s caller owner amount = none

abbrev Properties.overflowing_mint_rejected {s : State} {caller recipient : Address}
    {amount : UInt256} (h : UInt256.size ≤ s.totalSupply + amount.val) :=
  mint s caller recipient amount = none

/-- Non-vacuity of the model statements above. For any configuration with a nonzero vault and any
nonzero account: the empty ledger is `WellFormed`, the vault's one-unit mint to the account succeeds
to a `WellFormed` ledger, and the vault's one-unit burn from it returns exactly the empty ledger. So
the premises of `burn_exact`, `mint_exact` and `reachable_ledger` are met by model calls. The
witness for the deployed headlines is `nonlegacy_one_unit_roundtrip`
(`Properties/LegacyFallback.lean`), which is proved from this one. -/
abbrev Properties.one_unit_roundtrip (config : Config) (account : Address)
    (hv : config.vault ≠ 0) (ha : account ≠ 0) :=
  WellFormed (empty config) ∧
  ∃ funded, mint (empty config) config.vault account 1 = some funded ∧
    WellFormed funded ∧ burn funded config.vault account 1 = some (empty config)

end Contracts.BridgedStandardERC20
