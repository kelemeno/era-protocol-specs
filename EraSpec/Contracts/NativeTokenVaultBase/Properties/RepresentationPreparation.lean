import EraSpec.Contracts.NativeTokenVaultBase.Specs.RepresentationPreparation

set_option linter.unusedVariables false

namespace Contracts.NativeTokenVaultBase

variable {Accounting : Type}

/-- Successful preparation performs a real operation of the local token model;
exact debit/supply accounting is derived from the token invariant, not assumed. -/
abbrev Properties.preparation_backed {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request} {out : Result Accounting} (hw : WellFormed s)
    (h : prepare hooks s r = some out) :=
  BridgedStandardERC20.burn s.token s.config.vault r.depositor r.data.amount = some out.state.token ∧
  out.state.token.balances r.depositor + out.data.amount.val = s.token.balances r.depositor ∧
  out.state.token.totalSupply + out.data.amount.val = s.token.totalSupply ∧
  out.data.amount ≠ 0

abbrev Properties.preparation_payload {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request} {out : Result Accounting} (hw : WellFormed s)
    (h : prepare hooks s r = some out) :=
  out.data.originalCaller = r.depositor ∧ out.data.remoteReceiver = r.data.receiver ∧
  out.data.originToken = s.token.config.originToken ∧ out.data.amount = r.data.amount ∧
  out.data.originToken ≠ 0 ∧
  hooks.metadata out.state.token s.config.originChainId = some out.data.metadata

/-- Hook receives the pre-burn snapshot and exact destination/asset/amount. -/
abbrev Properties.preparation_accounting {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request} {out : Result Accounting} (h : prepare hooks s r = some out) :=
  hooks.account s.accounting s.token r.destinationChain r.assetId r.data.amount =
    some out.state.accounting

/-- The actual reverse-map guard plus tracked-registry consistency rules out
labeling this token's burn as preparation for a different asset. -/
abbrev Properties.preparation_asset_binding {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request} {out : Result Accounting} (hw : WellFormed s)
    (h : prepare hooks s r = some out) :=
  r.assetId = s.config.assetId ∧ out.state.token.config.assetId = r.assetId ∧
  selectedToken s r = s.config.tokenAddress

abbrev Properties.preparation_preserves_ledger {hooks : Hooks Accounting}
    {s : State Accounting} {r : Request} {out : Result Accounting}
    (hw : WellFormed s) (h : prepare hooks s r = some out) :=
  WellFormed out.state ∧ out.state.config = s.config ∧ out.state.registry = s.registry ∧
  out.state.paused = s.paused ∧
  ∀ other, other ≠ r.depositor → out.state.token.balances other = s.token.balances other

/-- Economic accounting is preserved without assuming agreement of identities. -/
abbrev Properties.preparation_preserves_ledger_invariant {hooks : Hooks Accounting}
    {s : State Accounting} {r : Request} {out : Result Accounting}
    (hl : LedgerInvariant s) (h : prepare hooks s r = some out) := LedgerInvariant out.state

/-- Identity agreement is preserved without assuming valid token balances. -/
abbrev Properties.preparation_preserves_representation {hooks : Hooks Accounting}
    {s : State Accounting} {r : Request} {out : Result Accounting}
    (hr : RepresentationConsistent s) (h : prepare hooks s r = some out) :=
  RepresentationConsistent out.state

/-- Both the token and the accounting snapshot are restored on any failed call. -/
abbrev Properties.failed_preparation_atomic {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request} (h : prepare hooks s r = none) := transact hooks s r = (s, none)

/-- Even a failure after a tentative token burn commits no source debit. -/
abbrev Properties.metadata_failure_atomic {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request} (h : ∀ token, hooks.metadata token s.config.originChainId = none) :=
  transact hooks s r = (s, none)

abbrev Properties.accounting_failure_atomic {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request}
    (h : hooks.account s.accounting s.token r.destinationChain r.assetId r.data.amount = none) :=
  transact hooks s r = (s, none)

/-- Readiness is not defined as success. Sufficient balance, valid identities,
and successful named dependencies imply an actual successful preparation. -/
abbrev Properties.preparation_enabled {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request} {accounted : Accounting} {metadata : Bytes}
    (hw : WellFormed s) (hs : InScope s r) (he : EntryAllowed s r)
    (hv : r.msgValue = 0) (hd : r.depositor ≠ 0)
    (hb : r.data.amount.val ≤ s.token.balances r.depositor)
    (ho : s.token.config.originToken ≠ 0) (hc : s.config.originChainId ≠ 0)
    (ha : hooks.account s.accounting s.token r.destinationChain r.assetId r.data.amount =
      some accounted)
    (hm : hooks.metadata (BridgedStandardERC20.burnEffect s.token r.depositor r.data.amount)
      s.config.originChainId = some metadata) :=
  ∃ out, prepare hooks s r = some out

end Contracts.NativeTokenVaultBase
