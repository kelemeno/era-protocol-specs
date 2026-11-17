import EraSpec.Contracts.NativeTokenVaultBase.Specs.Resolution
import EraSpec.Contracts.L2AssetTracker.Specs.Accounting

/-!
# The concrete chain-balance hooks: the L1 vault's `bridgedOut`, and the L2 asset tracker

`Specs/RepresentationPreparation.lean` and `Specs/Resolution.lean` leave the two chain-balance
hooks abstract (`Hooks.account`, `ResolutionHooks.fromChain`), and the round trip
`Properties.PrepareThenRecoverRoundTrip` takes their inverse law `HooksCancel` as a premise.
This file supplies the deployed hooks at source pin `c67894b970a0dac6fe9144d8ebf4b0806e15a9af`
(`l1-contracts/contracts/`):

* **L1** (`bridge/ntv/L1NativeTokenVault.sol:259-277`, cited `L1NTV`):

      function _handleBridgeToChain(uint256, bytes32 _assetId, uint256 _amount) internal override {
          if (originChainId[_assetId] == block.chainid) { bridgedOut[_assetId] += _amount; }
      }
      function _handleBridgeFromChain(uint256 _chainId, bytes32 _assetId, uint256 _amount) internal override {
          if (originChainId[_assetId] == block.chainid) {
              if (bridgedOut[_assetId] < _amount) revert InsufficientChainBalance(...);
              bridgedOut[_assetId] -= _amount;
          }
      }

  `L1Ledger` holds the two maps the hooks touch (`L1NTV:73`, and the vault's `originChainId`,
  which the hooks only read); `block.chainid` is a parameter.  `+=` is checked
  (`L2AssetTracker.checkedAdd`, `SOL-ARITH`).  The chain argument is unnamed in the outbound hook
  and only reported in the inbound one's error, so the ledger is aggregated over chains.

* **L2** (`bridge/ntv/L2NativeTokenVault.sol:296-315`): the two hooks call
  `L2AssetTracker.handleInitiateBridgingOnL2(_chainid, _assetId, _amount, originChainId[_assetId])`
  and `handleFinalizeBridgingOnL2(_chainId, _assetId, _amount, originChainId[_assetId],
  tokenAddress[_assetId])`, modelled in `Contracts.L2AssetTracker` (`Specs/Accounting.lean`).
  The accounting state is the tracker's storage together with the current settlement layer
  (`L2Accounting`); the vault's own maps are the tracker `Config`.  The token snapshot the
  hooks receive is what the tracker's first-touch registration reads
  (`L2AssetTracker.tokenReads`): the PRE-burn token for the outbound hook, the PRE-mint token for
  the inbound one.

## Where the hooks run

`bridgeRecoverFailedTransfer` has one caller, `L2AssetRouter.recoverAtomicCall`
(`bridge/asset-router/L2AssetRouter.sol:294`); on L1 the vault's refund is
`bridgeConfirmTransferResult` (`L1NTV:182-214`), which runs the same `_disburseFailedTransfer`
(`bridge/ntv/NativeTokenVaultBase.sol:284-306`) and so the same inbound hook.  The L1 round trip
below is therefore the hook half of the L1 failed-deposit refund, on the bridged branch the
resolution model covers.

## The weaker law the L2 tracker satisfies

The L2 tracker does not satisfy `HooksCancel`: a first-touch legacy registration persists, and
the L1 counters move in the same direction both ways.  `HooksCancelModulo hooks rh Off reg` is
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
written), `L1NTV:73`. -/
structure L1Ledger where
  /-- `originChainId[assetId]` (`NativeTokenVaultBase.sol`; read only by the hooks). -/
  originChainId : UInt256 → UInt256
  /-- `bridgedOut[assetId]` (`L1NTV:73`). -/
  bridgedOut : UInt256 → UInt256

/-- `_handleBridgeToChain(_, _assetId, _amount)` on L1 (`L1NTV:260-264`), with `block.chainid`
`thisChain`: checked `bridgedOut[_assetId] += _amount` for a native asset, nothing otherwise. -/
def l1ToChain (thisChain : UInt256) (acc : L1Ledger) (asset amount : UInt256) : Option L1Ledger :=
  if acc.originChainId asset = thisChain then
    (checkedAdd (acc.bridgedOut asset) amount).map fun v =>
      { acc with bridgedOut := Function.update acc.bridgedOut asset v }
  else some acc

/-- `_handleBridgeFromChain(_chainId, _assetId, _amount)` on L1 (`L1NTV:270-277`): for a native
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
(`L2NativeTokenVault.sol:296-302`), the tracker reading the PRE-burn token; the metadata
dependency is left as given. -/
def l2Hooks (cfg : L2AssetTracker.Config)
    (metadata : BridgedStandardERC20.State → UInt256 → Option Bytes) : Hooks L2Accounting :=
  ⟨fun acc tok chain asset amount =>
    (L2AssetTracker.handleInitiateBridgingOnL2 cfg acc.st acc.sl (L2AssetTracker.tokenReads cfg tok)
      cfg.ntv chain asset amount (cfg.ntvOriginChainId asset)).map fun st => { acc with st := st },
   metadata⟩

/-- The L2 vault's resolution hook: `_handleBridgeFromChain` is `handleFinalizeBridgingOnL2(chain,
asset, amount, originChainId[asset], tokenAddress[asset])` (`L2NativeTokenVault.sol:304-315`). -/
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

/-- The L2 round trip is accounting-neutral up to registration when the chain is not L1, or the
chain does not currently settle on L1 (`L2AssetTracker.sol:244-249, 299-304`). -/
def L2OffL1 (acc : L2Accounting) (chain : UInt256) : Prop :=
  chain ≠ acc.st.l1ChainId ∨ acc.sl ≠ acc.st.l1ChainId

/-- The L2 registration hook of a first bridge (`_setNewTokenStorage`, `L2NativeTokenVault.sol:186-188`):
`registerNewTokenIfNeeded(assetId, originChainId)` called by the vault. -/
def l2RegistrationHook (cfg : L2AssetTracker.Config) (acc : L2Accounting) (_ : Registry)
    (_ : BridgedStandardERC20.State) (asset origin : UInt256) : Option L2Accounting :=
  (L2AssetTracker.registerNewTokenIfNeeded cfg acc.st cfg.ntv asset origin).map
    fun st => { acc with st := st }

end Contracts.NativeTokenVaultBase
