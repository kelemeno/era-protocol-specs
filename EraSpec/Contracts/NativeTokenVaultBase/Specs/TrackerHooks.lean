import EraSpec.Contracts.NativeTokenVaultBase.Specs.Resolution
import EraSpec.Contracts.L2AssetTracker.Specs.Accounting

/-!
# The concrete chain-balance hooks: the L1 vault's `bridgedOut`, and the L2 asset tracker

`Specs/RepresentationPreparation.lean` and `Specs/Resolution.lean` leave the two chain-balance
hooks abstract (`Hooks.account`, `ResolutionHooks.fromChain`), and the round trip
`Properties.PrepareThenRecoverRoundTrip` takes their inverse law `HooksCancel` as a premise.
This file supplies the deployed hooks at `draft/v0.35.0` head `b17415d2068065a4a3e3f0e7a14a2e96f54212e5`
(`l1-contracts/contracts/`; first written at the pin `c67894b9`):

* **L1** (`bridge/ntv/L1NativeTokenVault.sol:424-459`, cited `L1NTV`): the `bridgedOut` part only.
  For an asset whose `originChainId` is `block.chainid`, `_handleBridgeToChain(chainId, assetId,
  amount)` adds `amount` to `bridgedOut[assetId]` (`L1NTV:426-428`), and
  `_handleBridgeFromChain(chainId, assetId, amount)` reverts with `InsufficientChainBalance` if
  `bridgedOut[assetId] < amount` and otherwise subtracts it (`L1NTV:440-445`); for any other asset
  that part does nothing.  At the pin (`L1NativeTokenVault.sol:259-277` there) this was the whole
  hook.  At `b17415d20` each hook then also adds the amount to the per-chain
  `chainTotalDeposited` or `chainTotalWithdrawn` of a tracked chain balance, and the inbound hook
  reverts when that exceeds the chain's cap (`L1NTV:429-432`, `:446-458`).  `L1Ledger` does not
  model those totals: L1NativeTokenVault `InteropPool` does, and `LedgerRefinement` there shows that
  every successful hook of that model is the `L1Ledger` hook on `bridgedOut` (the per-chain part
  only adds reverts).  So the L1 results here are about the `bridgedOut` ledger; `HooksCancel` does
  not hold of the whole `b17415d20` hooks, whose per-chain totals both grow on a round trip.

  `L1Ledger` holds the two maps the `bridgedOut` part touches (`L1NTV:90`, and the vault's
  `originChainId`, which the hooks only read); `block.chainid` is a parameter.  `+=` is checked
  (`L2AssetTracker.checkedAdd`, `SOL-ARITH`).  `bridgedOut` has no chain index.

* **L2** (`bridge/ntv/L2NativeTokenVault.sol:279-293`): the two hooks call
  `L2AssetTracker.handleInitiateBridgingOnL2(_chainid, _assetId, _amount, originChainId[_assetId])`
  and `handleFinalizeBridgingOnL2(_chainId, _assetId, _amount, originChainId[_assetId],
  tokenAddress[_assetId])`, modelled in `Contracts.L2AssetTracker` (`Specs/Accounting.lean`).
  The accounting state is the tracker's storage together with the current settlement layer
  (`L2Accounting`); the vault's own maps are the tracker `Config`.  The token snapshot the
  hooks receive is what the tracker's first-touch registration reads
  (`L2AssetTracker.tokenReads`): the PRE-burn token for the outbound hook, the PRE-mint token for
  the inbound one.  The vault model's `State.config` and `registry` and the tracker `Config` are
  separate parameters, not tied to each other: the results hold for every pair, and the
  witnesses use pairs that agree on the vault address, `block.chainid`, and the tracked asset's
  origin chain and token address.

## Where the hooks run

The vault's `bridgeRecoverFailedTransfer` has one caller, `L2AssetRouter.recoverAtomicCall`
(`bridge/asset-router/L2AssetRouter.sol:301`), so on L1 nothing calls it.  The L1 vault's refund
of a failed deposit is `bridgeConfirmTransferResult` (`L1NTV:351-380`), which runs the same
`_disburseFailedTransfer` (`bridge/ntv/NativeTokenVaultBase.sol:264-286`) and so the same inbound
hook.  With the L1 hooks, the resolution model's recovery therefore stands for that refund's hook
and mint only, not for its own checks and decoding.

## The weaker law the L2 tracker satisfies

The L2 tracker does not satisfy `HooksCancel`: a first-touch legacy registration persists, and,
for a transfer to L1 while the chain settles on L1, both L1 counters grow on a round trip.  `HooksCancelModulo hooks rh Off reg` is
what it does satisfy: whenever `Off` holds of the starting accounting and the chain, the
resolution hook undoes the preparation hook UP TO `reg`, a function of the starting accounting
and the pre-burn token.  `HooksCancel` is the case `Off := True`, `reg := some`.
-/

namespace Contracts.NativeTokenVaultBase

open Contracts.L2AssetTracker (checkedAdd checkedSub)

variable {Accounting : Type}

/-! ## The generalized cancel law -/

/-- **CANCELLATION UP TO A REGISTRATION.**  Whenever `Off a chain` holds and the preparation hook
takes `a` to `a'`, the resolution hook with the same chain, asset and amount succeeds from `a'`
(whatever token snapshot it sees) and gives `reg a before asset`, which must itself be defined. -/
def HooksCancelModulo (hooks : Hooks Accounting) (rh : ResolutionHooks Accounting)
    (Off : Accounting → UInt256 → Prop)
    (reg : Accounting → BridgedStandardERC20.State → UInt256 → Option Accounting) : Prop :=
  ∀ (a a' : Accounting) (before after : BridgedStandardERC20.State) (chain asset amount : UInt256),
    Off a chain → hooks.account a before chain asset amount = some a' →
      ∃ a₀, reg a before asset = some a₀ ∧ rh.fromChain a' after chain asset amount = some a₀

/-! ## L1: `bridgedOut` -/

/-- The L1 vault storage the hooks touch: `originChainId` (read) and `bridgedOut` (read and
written), `L1NTV:90`. -/
structure L1Ledger where
  /-- `originChainId[assetId]` (`NativeTokenVaultBase.sol`; read only by the hooks). -/
  originChainId : UInt256 → UInt256
  /-- `bridgedOut[assetId]` (`L1NTV:90`). -/
  bridgedOut : UInt256 → UInt256

/-- `_handleBridgeToChain(_, _assetId, _amount)` on L1, its `bridgedOut` part (`L1NTV:426-428`), with `block.chainid`
`thisChain`: checked `bridgedOut[_assetId] += _amount` for a native asset, nothing otherwise. -/
def l1ToChain (thisChain : UInt256) (acc : L1Ledger) (asset amount : UInt256) : Option L1Ledger :=
  if acc.originChainId asset = thisChain then
    (checkedAdd (acc.bridgedOut asset) amount).map fun v =>
      { acc with bridgedOut := Function.update acc.bridgedOut asset v }
  else some acc

/-- `_handleBridgeFromChain(_chainId, _assetId, _amount)` on L1, its `bridgedOut` part (`L1NTV:440-445`): for a native
asset, revert if `bridgedOut[_assetId] < _amount`, else subtract; nothing otherwise. -/
def l1FromChain (thisChain : UInt256) (acc : L1Ledger) (asset amount : UInt256) :
    Option L1Ledger :=
  if acc.originChainId asset = thisChain then
    (checkedSub (acc.bridgedOut asset) amount).map fun v =>
      { acc with bridgedOut := Function.update acc.bridgedOut asset v }
  else some acc

/-- The L1 vault's preparation hooks: the outbound chain-balance hook (it ignores the chain and
the token snapshot), and a metadata dependency left as given. -/
def l1Hooks (thisChain : UInt256) (metadata : BridgedStandardERC20.State → UInt256 → Option Bytes) :
    Hooks L1Ledger :=
  ⟨fun acc _ _ asset amount => l1ToChain thisChain acc asset amount, metadata⟩

/-- The L1 vault's resolution hook. -/
def l1ResolutionHooks (thisChain : UInt256) : ResolutionHooks L1Ledger :=
  ⟨fun acc _ _ asset amount => l1FromChain thisChain acc asset amount⟩

/-- The ledger agrees with the vault configuration about the tracked asset: its origin chain is
the configured one, and `block.chainid` is the configured chain. -/
def L1LedgerAgrees (thisChain : UInt256) (s : State L1Ledger) : Prop :=
  thisChain = s.config.chainId ∧ s.accounting.originChainId s.config.assetId = s.config.originChainId

/-! ## L2: the asset tracker -/

/-- What the L2 hooks read and write: the tracker's storage, and the chain's current settlement
layer (`currentSettlementLayerChainId()`, read by the tracker, written by migration). -/
structure L2Accounting where
  st : L2AssetTracker.Storage
  sl : UInt256

/-- The L2 vault's preparation hooks: `_handleBridgeToChain` is
`handleInitiateBridgingOnL2(chain, asset, amount, originChainId[asset])` called by the vault
(`L2NativeTokenVault.sol:279-283`), the tracker reading the PRE-burn token; the metadata
dependency is left as given. -/
def l2Hooks (cfg : L2AssetTracker.Config)
    (metadata : BridgedStandardERC20.State → UInt256 → Option Bytes) : Hooks L2Accounting :=
  ⟨fun acc tok chain asset amount =>
    (L2AssetTracker.handleInitiateBridgingOnL2 cfg acc.st acc.sl (L2AssetTracker.tokenReads cfg tok)
      cfg.ntv chain asset amount (cfg.ntvOriginChainId asset)).map fun st => { acc with st := st },
   metadata⟩

/-- The L2 vault's resolution hook: `_handleBridgeFromChain` is `handleFinalizeBridgingOnL2(chain,
asset, amount, originChainId[asset], tokenAddress[asset])` (`L2NativeTokenVault.sol:285-293`). -/
def l2ResolutionHooks (cfg : L2AssetTracker.Config) : ResolutionHooks L2Accounting :=
  ⟨fun acc tok chain asset amount =>
    (L2AssetTracker.handleFinalizeBridgingOnL2 cfg acc.st acc.sl (L2AssetTracker.tokenReads cfg tok)
      cfg.ntv chain asset amount (cfg.ntvOriginChainId asset) (cfg.ntvTokenAddress asset)).map
      fun st => { acc with st := st }⟩

/-- The registration the L2 round trip leaves behind: the tracker's first-touch
`_registerLegacyTokenIfNeeded(asset, tokenAddress[asset])`, reading the given (pre-burn) token.
For an already registered asset it is the identity. -/
def l2Registration (cfg : L2AssetTracker.Config) (acc : L2Accounting)
    (tok : BridgedStandardERC20.State) (asset : UInt256) : Option L2Accounting :=
  (L2AssetTracker.registerLegacyTokenIfNeeded cfg acc.st (L2AssetTracker.tokenReads cfg tok) asset
    (cfg.ntvTokenAddress asset)).map fun st => { acc with st := st }

/-- The L2 round trip is accounting-neutral up to registration when the other chain is not the
tracker's `L1_CHAIN_ID`, or this chain does not currently settle on L1
(`L2AssetTracker.sol:160-165, 223-228`). -/
def L2OffL1 (acc : L2Accounting) (chain : UInt256) : Prop :=
  chain ≠ acc.st.l1ChainId ∨ acc.sl ≠ acc.st.l1ChainId

/-- The L2 registration hook of a first bridge: `_setNewTokenStorage`
(`bridge/ntv/NativeTokenVaultBase.sol:565-575`) calls `_registerTokenInAssetTracker`
(`L2NativeTokenVault.sol:177-179`), which is `registerNewTokenIfNeeded(assetId, originChainId)`
called by the vault. -/
def l2RegistrationHook (cfg : L2AssetTracker.Config) (acc : L2Accounting) (_ : Registry)
    (_ : BridgedStandardERC20.State) (asset origin : UInt256) : Option L2Accounting :=
  (L2AssetTracker.registerNewTokenIfNeeded cfg acc.st cfg.ntv asset origin).map
    fun st => { acc with st := st }

end Contracts.NativeTokenVaultBase
