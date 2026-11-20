import EraSpec.Contracts.L1NativeTokenVault.Specs.LedgerRefinement
import EraSpec.Core.Headline

/-!
# Properties: the `b17415d20` vault ledger refines the `bridgedOut`-only models

Statements about `EraSpec.Contracts.L1NativeTokenVault.Specs.LedgerRefinement`.  Proofs are in
`EraSpec.Contracts.L1NativeTokenVault.Proofs.LedgerRefinement`.  `l1` is L1's chain id
(`block.chainid`) and `o` the value of `originChainId[a]` when the hook runs.

* `PoolToChainIsL1ToChain`, `PoolFromChainIsL1FromChain`: a successful `InteropPool` hook is the
  `L1Ledger` hook on agreeing `bridgedOut` maps, and the results agree again.
* `PoolHooksAreRegistryLedgerSteps`: a successful `InteropPool` hook moves `bridgedOut` as the
  registry model's `bridgeOut`/`bridgeIn` does, and an inbound one meets that model's
  `InsufficientChainBalance` guard.
* `PoolPopulateIsPopulateAtHead`: a successful `populateBridgedOut` entry is `populateAtHead` on
  `bridgedOut`.
* `PoolOtherCallsKeepBridgedOut`: no other `InteropPool` call writes `bridgedOut`.
* `PerChainCapIsStricterThanL1Ledger` (countermodel): the converse of the inbound refinement fails.
* `LedgerRefinementWitness`: the premises of the outbound refinement hold with a nonzero native
  deposit that changes `bridgedOut`.
-/

namespace Contracts.L1NativeTokenVault.LedgerRefinement

open Contracts.L1NativeTokenVault.InteropPool

/-- **A `b17415d20` deposit hook is the `L1Ledger` deposit hook.** -/
def Properties.PoolToChainIsL1ToChain : Prop :=
  ∀ (l1 : ChainId) (s s' : PoolSys) (c a : ChainId) (x : UInt256) (o : ChainId)
    (acc : NativeTokenVaultBase.L1Ledger),
    L1LedgerMatches acc s → acc.originChainId a = o →
    handleBridgeToChain l1 s c a x o = some s' →
      ∃ acc', NativeTokenVaultBase.l1ToChain l1 acc a x = some acc' ∧
        acc'.originChainId = acc.originChainId ∧ L1LedgerMatches acc' s'

/-- **A `b17415d20` withdrawal or failed-deposit hook is the `L1Ledger` inbound hook.** -/
def Properties.PoolFromChainIsL1FromChain : Prop :=
  ∀ (l1 : ChainId) (s s' : PoolSys) (c a : ChainId) (x : UInt256) (o : ChainId)
    (acc : NativeTokenVaultBase.L1Ledger),
    L1LedgerMatches acc s → acc.originChainId a = o →
    handleBridgeFromChain l1 s c a x o = some s' →
      ∃ acc', NativeTokenVaultBase.l1FromChain l1 acc a x = some acc' ∧
        acc'.originChainId = acc.originChainId ∧ L1LedgerMatches acc' s'

/-- **The `b17415d20` hooks move `bridgedOut` as the registry model's flows do.**  With the
registry's origin chain for `a` equal to `o` and its `bridgedOut` equal to `InteropPool`'s: after a
successful deposit hook, the registry's `bridgeOut` of the same amount has `InteropPool`'s new
`bridgedOut`; after a successful inbound hook, the registry's inbound guard
`InsufficientChainBalance` holds and its `bridgeIn` has `InteropPool`'s new `bridgedOut`. -/
def Properties.PoolHooksAreRegistryLedgerSteps : Prop :=
  ∀ (l1 : ChainId) (s s' : PoolSys) (c a : ChainId) (x : UInt256) (o : ChainId)
    (W : NativeTokenVault.World),
    W.vault.originChain a = o → RegistryLedgerMatches W.vault s →
    (handleBridgeToChain l1 s c a x o = some s' →
      RegistryLedgerMatches (NativeTokenVault.bridgeOut l1 W c a x.val).vault s') ∧
    (handleBridgeFromChain l1 s c a x o = some s' →
      (NativeTokenVault.Native l1 W.vault a → x.val ≤ W.vault.bridgedOut a) ∧
      RegistryLedgerMatches (NativeTokenVault.bridgeIn l1 W c a x.val).vault s')

/-- **A `b17415d20` population entry is `EscrowLedgerAtHead`'s.**  With the legacy amount of `a`
equal to the populated amount and agreeing `bridgedOut` maps, `populateAtHead` gives
`InteropPool`'s new `bridgedOut`. -/
def Properties.PoolPopulateIsPopulateAtHead : Prop :=
  ∀ (s s' : PoolSys) (a : AssetId) (amount : UInt256) (W : NativeTokenVault.WorldAtHead)
    (legacy : NativeTokenVault.LegacyAmounts),
    legacy a = amount.val → RegistryLedgerMatches W.world.vault s →
    populateBridgedOutEntry s a amount = some s' →
      RegistryLedgerMatches (NativeTokenVault.populateAtHead legacy W a).world.vault s'

/-- **Only the hooks and the population write `bridgedOut`.** -/
def Properties.PoolOtherCallsKeepBridgedOut : Prop :=
  ∀ (l1 : ChainId) (call : PoolCall) (s s' : PoolSys),
    ¬ WritesBridgedOut call → poolCall l1 call s = some s' → s'.bridgedOut = s.bridgedOut

/-- **COUNTERMODEL: the per-chain cap rejects what `L1Ledger` accepts.**  On agreeing ledgers,
for an L1-native asset, the `L1Ledger` inbound hook succeeds for a nonzero amount while the
`b17415d20` hook reverts (`ChainBalanceExceeded`, `L1NTV:452-454`).  So the refinement is one-way. -/
@[countermodel] def Properties.PerChainCapIsStricterThanL1Ledger : Prop :=
  ∃ (l1 : ChainId) (s : PoolSys) (c a : ChainId) (x : UInt256)
    (acc : NativeTokenVaultBase.L1Ledger),
    L1LedgerMatches acc s ∧ acc.originChainId a = l1 ∧ x ≠ 0 ∧
    (NativeTokenVaultBase.l1FromChain l1 acc a x).isSome ∧
    handleBridgeFromChain l1 s c a x l1 = none

/-- **The outbound refinement's premises, met non-trivially.**  Agreeing ledgers, an L1-native
asset, a nonzero deposit that succeeds and changes `bridgedOut`. -/
@[witness] def Properties.LedgerRefinementWitness : Prop :=
  ∃ (l1 : ChainId) (s s' : PoolSys) (c a : ChainId) (x : UInt256)
    (acc : NativeTokenVaultBase.L1Ledger),
    L1LedgerMatches acc s ∧ acc.originChainId a = l1 ∧ x ≠ 0 ∧
    handleBridgeToChain l1 s c a x l1 = some s' ∧ s'.bridgedOut a ≠ s.bridgedOut a

end Contracts.L1NativeTokenVault.LedgerRefinement
