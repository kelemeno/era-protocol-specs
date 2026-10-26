import EraSpec.Contracts.NativeTokenVaultBase.Specs.RepresentationPreparation
import EraSpec.Contracts.BridgedStandardERC20.Specs.Initialization

/-!
# New representation deployment and registry installation

Source projection of `_ensureAndSaveTokenDeployedInner` → `_deployBridgedToken`
→ `bridgeInitialize` → `_setNewTokenStorage`, at the recorded c678... pin.
`RegistrationState` has no tracked token yet. The deploy dependency represents
allocation of a NEW proxy with zeroed storage; its actual address is checked
against the expected `config.tokenAddress` only AFTER token initialization.
`config` identifies the tracked deployment context, not a Solidity config struct.

The asset encoder and deployer are explicit dependencies, not cryptographic or
CREATE2 proofs. The metadata flag represents outer decoding/setup success; caught
name/symbol/decimals decoding failures need not make that flag false. The tracker
hook sees the installed registry and initialized token and may reject the result.

Only the two maps represented by this slice are projected: origin-chain storage,
enumeration/index/count, metadata contents, full tracker behavior, proxies, and
transaction rollback correspondence remain open. No global no-alias theorem is
claimed. The `registerFreshBranch` wrapper models the caller's missing-forward-slot
branch; the inner registry-write helper itself has no such guard in Solidity.
-/

namespace Contracts.NativeTokenVaultBase

structure RegistrationState (Accounting : Type) where
  config : Config
  registry : Registry
  paused : Bool
  accounting : Accounting

structure RegistrationHooks (Accounting : Type) where
  assetIdFor : UInt256 → Address → UInt256
  deploy : UInt256 → Address → Option Address
  metadataDecoded : Bool
  registerTracker : Accounting → Registry → BridgedStandardERC20.State →
    UInt256 → UInt256 → Option Accounting

structure Registered (Accounting : Type) where
  state : State Accounting
  tokenVersion : UInt8

/-- The source writes these map slots independently. Their agreement is proved
from the common call arguments, not imposed by a type-level identification. -/
def installRegistry (registry : Registry) (asset : UInt256) (token : Address) : Registry :=
  ⟨Function.update registry.tokenForAsset asset token,
    Function.update registry.assetForToken token asset⟩

/-- The projected ledger of a successfully initialized fresh proxy. -/
def registeredToken (config : Config) (origin : Address) : BridgedStandardERC20.State :=
  BridgedStandardERC20.empty ⟨config.vault, origin, config.assetId⟩

variable {Accounting : Type}

def registerRepresentation (hooks : RegistrationHooks Accounting) (s : RegistrationState Accounting)
    (origin : Address) : Option (Registered Accounting) :=
  if s.config.assetId = hooks.assetIdFor s.config.originChainId origin ∧
      s.config.originChainId ≠ s.config.chainId then
    match hooks.deploy s.config.originChainId origin with
    | none => none
    | some deployed =>
      match BridgedStandardERC20.initializeToken BridgedStandardERC20.freshProxy
          s.config.vault s.config.assetId origin hooks.metadataDecoded with
      | none => none
      | some initialized =>
        if deployed = s.config.tokenAddress then
          let registry := installRegistry s.registry s.config.assetId deployed
          match hooks.registerTracker s.accounting registry initialized.token
              s.config.assetId s.config.originChainId with
          | none => none
          | some accounting => some ⟨⟨s.config, registry, s.paused, initialized.token, accounting⟩,
              initialized.version⟩
        else none
  else none

def registerFreshBranch (hooks : RegistrationHooks Accounting) (s : RegistrationState Accounting)
    (origin : Address) : Option (Registered Accounting) :=
  if s.registry.tokenForAsset s.config.assetId = 0 then registerRepresentation hooks s origin
  else none

end Contracts.NativeTokenVaultBase
