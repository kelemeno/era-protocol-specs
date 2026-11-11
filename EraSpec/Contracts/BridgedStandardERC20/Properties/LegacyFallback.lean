import EraSpec.Contracts.BridgedStandardERC20.Specs.LegacyFallback

-- Preconditions are retained as statement parameters for the full-proof audit.
set_option linter.unusedVariables false

/-!
# Properties: the legacy zero-vault fallback in `onlyNTV`

Statements about `EraSpec.Contracts.BridgedStandardERC20.Specs.LegacyFallback`. Proofs are
in `EraSpec.Contracts.BridgedStandardERC20.Proofs.LegacyFallback`.

* **Conservative.** On a token with a nonzero vault the bridge calls are the nonlegacy
  model's `mint` and `burn` (`nonlegacy_bridge_calls_unchanged`), the two models have the
  same runs (`nonlegacy_runs_agree`), and every nonlegacy-model run is a run of the deployed
  token (`original_runs_are_legacy_runs`). On a legacy token the nonlegacy model refuses
  every bridge call (`original_model_rejects_legacy`) and only transfers.
* **The first bridge call.** On a legacy token only the L2 vault can make a bridge call
  (`legacy_unauthorized_bridge_calls`). When it does, the call installs exactly the fallback
  configuration (vault `L2_NATIVE_TOKEN_VAULT_ADDR`, asset id
  `encodeNTVAssetId(L1_CHAIN_ID, originToken)`, origin token unchanged) and has exactly the
  nonlegacy ledger effect (`legacy_bridge_mint_exact`, `legacy_bridge_burn_exact`). The
  branch is live (`legacy_bridge_mint_enabled`, `legacy_bridge_burn_enabled`).
* **At most once.** After any successful bridge call the token is nonlegacy
  (`bridge_call_ends_nonlegacy`). Along any run the configuration is the starting one or the
  fallback configuration computed from the starting origin token (`legacy_run_config`,
  `legacy_run_fallback_fired`). So the asset-id slot is written at most once, from the
  origin token the token already held, and `L1_CHAIN_ID` is read by at most one committed
  call.
* **Then the nonlegacy branch.** The runs from a legacy token are exactly: a run of the
  nonlegacy model (transfers only), or such a run, then one nonlegacy `mint` or `burn` from
  the same ledger with the fallback configuration, then a run of the nonlegacy model
  (`legacy_runs_characterized`). Every nonlegacy result therefore applies after the first
  bridge call. The ledger invariant holds along every run (`legacy_reachable_ledger`).

`legacy_branch_witness` meets the premises of the legacy-branch statements for every
environment and origin token, including a successful call the nonlegacy model refuses.

Whether the id the fallback writes is the vault's id for the token is a question about the
vault's registry, which the fallback does not read. It is answered in
`EraSpec.Contracts.NativeTokenVaultBase.Properties.LegacyFallback`.
-/

namespace Contracts.BridgedStandardERC20

/-! ## The extension is conservative -/

/-- The trustee the fallback installs is not the zero address. -/
abbrev Properties.l2_vault_nonzero := l2NativeTokenVaultAddr ≠ 0

/-- **ON A NONLEGACY TOKEN THE BRIDGE CALLS ARE THE NONLEGACY MODEL'S.** With a nonzero vault
the prologue writes nothing, so `bridgeMint` and `bridgeBurn` are exactly `mint` and `burn`,
whatever `L1_CHAIN_ID` returns and whatever the encoder is. -/
abbrev Properties.nonlegacy_bridge_calls_unchanged (env : LegacyEnv) {s : State}
    (h : s.config.vault ≠ 0) (caller account : Address) (amount : UInt256) :=
  bridgeMint env s caller account amount = mint s caller account amount ∧
  bridgeBurn env s caller account amount = burn s caller account amount

/-- **THE NONLEGACY MODEL REFUSES EVERY BRIDGE CALL ON A LEGACY TOKEN.** The deployed token
does not (`legacy_branch_witness`), so the nonlegacy model's `none` on a zero vault is a scope
restriction, not the contract's behavior. -/
abbrev Properties.original_model_rejects_legacy {s : State} (h : s.config.vault = 0)
    (caller account : Address) (amount : UInt256) :=
  mint s caller account amount = none ∧ burn s caller account amount = none

/-- In the nonlegacy model a legacy token can only transfer. -/
abbrev Properties.legacy_original_steps_are_transfers {s t : State} (hl : s.config.vault = 0)
    (h : Step s t) :=
  ∃ owner recipient amount, transfer s owner recipient amount = some t

/-- **EVERY RUN OF THE NONLEGACY MODEL IS A RUN OF THE DEPLOYED TOKEN.** -/
abbrev Properties.original_runs_are_legacy_runs (env : LegacyEnv) {s t : State}
    (h : Reach s t) :=
  LegacyReach env s t

/-- **FROM A NONLEGACY TOKEN THE TWO MODELS HAVE THE SAME RUNS.** -/
abbrev Properties.nonlegacy_runs_agree (env : LegacyEnv) {s : State} (h : s.config.vault ≠ 0)
    (t : State) :=
  LegacyReach env s t ↔ Reach s t

/-! ## The legacy branch, call by call -/

/-- **A LEGACY BRIDGE MINT.** The caller was the L2 vault. The post-state carries exactly the
fallback configuration, and the ledger moves exactly as in the nonlegacy `mint`: the recipient
and the supply gain the amount, every other balance is unchanged. -/
abbrev Properties.legacy_bridge_mint_exact (env : LegacyEnv) {s t : State}
    {caller recipient : Address} {amount : UInt256} (hl : s.config.vault = 0)
    (h : bridgeMint env s caller recipient amount = some t) :=
  caller = l2NativeTokenVaultAddr ∧ t.config = fallbackConfig env s.config ∧
  t.balances recipient = s.balances recipient + amount.val ∧
  t.totalSupply = s.totalSupply + amount.val ∧
  (∀ other, other ≠ recipient → t.balances other = s.balances other)

/-- **A LEGACY BRIDGE BURN.** As `legacy_bridge_mint_exact`: the caller was the L2 vault, the
post-state carries exactly the fallback configuration, and the owner and the supply lose
exactly the amount. No allowance is involved. -/
abbrev Properties.legacy_bridge_burn_exact (env : LegacyEnv) {s t : State}
    {caller owner : Address} {amount : UInt256} (hw : WellFormed s) (hl : s.config.vault = 0)
    (h : bridgeBurn env s caller owner amount = some t) :=
  caller = l2NativeTokenVaultAddr ∧ t.config = fallbackConfig env s.config ∧
  t.balances owner + amount.val = s.balances owner ∧
  t.totalSupply + amount.val = s.totalSupply ∧
  (∀ other, other ≠ owner → t.balances other = s.balances other)

/-- **ONLY THE L2 VAULT TAKES THE FALLBACK.** On a legacy token every bridge call by any other
caller fails. `none` commits nothing, so the prologue's two writes are rolled back with the
call and the token stays legacy. In particular the deprecated `l2Bridge` has no authority. -/
abbrev Properties.legacy_unauthorized_bridge_calls (env : LegacyEnv) {s : State}
    {caller : Address} (hl : s.config.vault = 0) (hc : caller ≠ l2NativeTokenVaultAddr)
    (account : Address) (amount : UInt256) :=
  bridgeMint env s caller account amount = none ∧ bridgeBurn env s caller account amount = none

/-- **THE LEGACY MINT IS LIVE.** The L2 vault's mint to a nonzero recipient within the supply
bound succeeds, with the nonlegacy mint effect on the fallback-configured token. -/
abbrev Properties.legacy_bridge_mint_enabled (env : LegacyEnv) {s : State}
    {recipient : Address} {amount : UInt256} (hl : s.config.vault = 0) (hr : recipient ≠ 0)
    (hs : s.totalSupply + amount.val < UInt256.size) :=
  bridgeMint env s l2NativeTokenVaultAddr recipient amount
    = some (mintEffect { s with config := fallbackConfig env s.config } recipient amount)

/-- **THE LEGACY BURN IS LIVE.** The L2 vault's burn from a nonzero owner holding the amount
succeeds, with the nonlegacy burn effect on the fallback-configured token. -/
abbrev Properties.legacy_bridge_burn_enabled (env : LegacyEnv) {s : State}
    {owner : Address} {amount : UInt256} (hl : s.config.vault = 0) (ho : owner ≠ 0)
    (hb : amount.val ≤ s.balances owner) :=
  bridgeBurn env s l2NativeTokenVaultAddr owner amount
    = some (burnEffect { s with config := fallbackConfig env s.config } owner amount)

/-- **AFTER ANY SUCCESSFUL BRIDGE CALL THE TOKEN IS NONLEGACY.** On either branch the caller
was the post-state's vault, the post-state carries the prologue's configuration, and that
vault is nonzero, so no later call takes the fallback. -/
abbrev Properties.bridge_call_ends_nonlegacy (env : LegacyEnv) {s t : State}
    {caller account : Address} {amount : UInt256}
    (h : bridgeMint env s caller account amount = some t ∨
      bridgeBurn env s caller account amount = some t) :=
  caller = t.config.vault ∧ t.config = (legacyFallback env s).config ∧ t.config.vault ≠ 0

/-! ## Runs: the fallback fires at most once -/

/-- One step keeps the configuration, or takes the fallback from a legacy token. -/
abbrev Properties.legacy_step_config (env : LegacyEnv) {s t : State}
    (h : LegacyStep env s t) :=
  t.config = s.config ∨ (s.config.vault = 0 ∧ t.config = fallbackConfig env s.config)

/-- **THE ASSET ID IS WRITTEN AT MOST ONCE.** Along any run the configuration is the starting
one or, only if the run started legacy, the fallback configuration computed from the starting
origin token. -/
abbrev Properties.legacy_run_config (env : LegacyEnv) {s t : State}
    (h : LegacyReach env s t) :=
  t.config = s.config ∨ (s.config.vault = 0 ∧ t.config = fallbackConfig env s.config)

/-- **ONCE THE VAULT IS SET, THE CONFIGURATION IS EXACTLY THE FALLBACK'S.** On a run from a
legacy token that has reached a nonzero vault, the vault is the L2 vault and the asset id is
`encodeNTVAssetId(L1_CHAIN_ID, originToken)` for the starting origin token. -/
abbrev Properties.legacy_run_fallback_fired (env : LegacyEnv) {s t : State}
    (hl : s.config.vault = 0) (h : LegacyReach env s t) (hv : t.config.vault ≠ 0) :=
  t.config = fallbackConfig env s.config

/-- **THEN IT BEHAVES AS THE NONLEGACY BRANCH.** The runs of the deployed token from a legacy
token are exactly these: a run of the nonlegacy model (which, from a legacy token, transfers
only and keeps the configuration); or such a run to some `u`, then one nonlegacy-model `mint`
or `burn` from `u`'s ledger with the fallback configuration, then a run of the nonlegacy
model. -/
abbrev Properties.legacy_runs_characterized (env : LegacyEnv) {s : State}
    (hl : s.config.vault = 0) (t : State) :=
  LegacyReach env s t ↔
    (Reach s t ∧ t.config = s.config) ∨
    ∃ u u', Reach s u ∧ u.config = s.config ∧
      ((∃ caller recipient amount,
          mint { u with config := fallbackConfig env s.config } caller recipient amount
            = some u') ∨
        (∃ caller owner amount,
          burn { u with config := fallbackConfig env s.config } caller owner amount
            = some u')) ∧
      Reach u' t

/-- **THE LEDGER INVARIANT HOLDS ALONG EVERY RUN, BOTH BRANCHES**, and the origin token never
changes. -/
abbrev Properties.legacy_reachable_ledger (env : LegacyEnv) {s t : State} (hw : WellFormed s)
    (h : LegacyReach env s t) :=
  WellFormed t ∧ t.config.originToken = s.config.originToken

/-! ## Non-vacuity -/

/-- **WITNESS.** For every environment, origin token and nonzero account: an empty legacy
token on which the L2 vault's one-unit mint succeeds where the nonlegacy model refuses it,
installing the fallback configuration; and a funded legacy token on which the L2 vault's
one-unit burn succeeds where the nonlegacy model refuses it, and which has a nonlegacy-model
step. These meet the premises of the legacy-branch statements above:
`legacy_bridge_mint_exact`, `legacy_bridge_burn_exact`, the two `…_enabled` statements,
`legacy_run_fallback_fired`, `bridge_call_ends_nonlegacy`,
`legacy_original_steps_are_transfers` and, with caller `0` (`l2_vault_nonzero`),
`legacy_unauthorized_bridge_calls`. -/
abbrev Properties.legacy_branch_witness (env : LegacyEnv) (origin account : Address)
    (ha : account ≠ 0) :=
  ∃ s₀ t₀ s₁ t₁ : State,
    WellFormed s₀ ∧ s₀.config.vault = 0 ∧ s₀.config.originToken = origin ∧
    mint s₀ l2NativeTokenVaultAddr account 1 = none ∧
    bridgeMint env s₀ l2NativeTokenVaultAddr account 1 = some t₀ ∧
    LegacyReach env s₀ t₀ ∧ t₀.config = fallbackConfig env s₀.config ∧
    t₀.config.vault ≠ 0 ∧ t₀.balances account = 1 ∧
    WellFormed s₁ ∧ s₁.config.vault = 0 ∧ s₁.config.originToken = origin ∧
    s₁.balances account = 1 ∧ (∃ u, Step s₁ u) ∧
    burn s₁ l2NativeTokenVaultAddr account 1 = none ∧
    bridgeBurn env s₁ l2NativeTokenVaultAddr account 1 = some t₁ ∧
    t₁.config = fallbackConfig env s₁.config ∧ t₁.totalSupply = 0

end Contracts.BridgedStandardERC20
