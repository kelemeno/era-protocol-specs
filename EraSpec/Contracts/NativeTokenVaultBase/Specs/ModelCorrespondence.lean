import EraSpec.Contracts.NativeTokenVaultBase.Specs.Initialization
import EraSpec.Contracts.NativeTokenVaultBase.Specs.RegistryAndEscrow

/-!
# Correspondence between the two native-token-vault models

This folder holds two independently written models of `NativeTokenVaultBase.sol`
(era-contracts `c67894b970a0dac6fe9144d8ebf4b0806e15a9af`):

* the representation model, namespace `Contracts.NativeTokenVaultBase`
  (`Specs/RepresentationPreparation.lean`, `Specs/Initialization.lean`): ONE tracked
  bridged token, its two registry maps `tokenForAsset` / `assetForToken`, the
  fresh-deployment registration (`registerRepresentation`, `registerFreshBranch`) and
  the non-native `bridgeBurn` preparation (`prepare`);
* the registry model, namespace `Contracts.NativeTokenVault`
  (`Specs/RegistryAndEscrow.lean`): all three registry maps `originChainId`,
  `tokenAddress`, `assetId`, both registration paths and the escrow ledger.

**This file is definitions only.**  It adds no transition to either model and
changes neither.  Statements are in
`EraSpec.Contracts.NativeTokenVaultBase.Properties.ModelCorrespondence`.

## What overlaps, and how it is related

| Source storage / value | Representation model | Registry model |
|---|---|---|
| `tokenAddress[assetId]` | `registry.tokenForAsset` (160-bit) | `Vault.token` (256-bit word) |
| `assetId[token]` | `registry.assetForToken` (160-bit key) | `Vault.assetOf` (256-bit key) |
| `originChainId[assetId]` | `config.originChainId`, tracked asset only | `Vault.originChain` |
| bridged token's `originToken()` | `token.config.originToken`, tracked asset only | `Vault.originToken` |
| `block.chainid` | `config.chainId` | `thisChain` |

The address types differ: the representation model uses `Fin (2^160)`, the registry
model a 256-bit word.  `widen` is the zero extension Solidity applies when an
`address` is stored or hashed as a word.  Registry-model keys outside the 160-bit
range are not addresses; `RegistryCorr` requires them unset.

The representation model has no `originChainId` map, only the configured origin
chain of its one tracked asset.  So `Corr` relates origin data for the tracked asset
only, and only once the registry model has it registered; origin data of every
other asset is unconstrained by the correspondence.

## Model boundaries

Not related here, because only one model has them: the escrow ledger and flow
audit (registry model only), native-token registration (registry model only), the
token ledger, accounting hook, pause flag, router and request fields
(representation model only), the token list / index / count (neither).
`registerFreshBranch` is compared with the registry model's `registerBridged`, and
`prepare` with the registry model's `bridgeOut` on a non-native asset; no other
operation pair is related.
-/

namespace Contracts.NativeTokenVaultBase

/-- `uint256(uint160(t))`: a 160-bit address as the 256-bit word the registry model
uses for addresses. -/
def widen (t : Address) : NativeTokenVault.Address :=
  ⟨t.val, lt_of_lt_of_le t.isLt (by unfold UInt256.size; norm_num)⟩

/-- The representation model's two registry maps, read as the registry model's
`tokenAddress` and `assetId` storage. -/
structure RegistryCorr (R : Registry) (V : NativeTokenVault.Vault) : Prop where
  /-- `tokenAddress[a]` agrees for every asset id. -/
  token : ∀ a, V.token a = widen (R.tokenForAsset a)
  /-- `assetId[t]` agrees for every address. -/
  assetOf : ∀ t : Address, V.assetOf (widen t) = R.assetForToken t
  /-- A word that is not an address carries no asset id. -/
  assetOfWide : ∀ w : NativeTokenVault.Address, (∀ t : Address, widen t ≠ w) → V.assetOf w = 0

variable {Accounting : Type}

/-- Correspondence of a registration pre-state: same chain, same two maps. -/
def CorrPre (s : RegistrationState Accounting) (thisChain : NativeTokenVault.Chain)
    (V : NativeTokenVault.Vault) : Prop :=
  thisChain = s.config.chainId ∧ RegistryCorr s.registry V

/-- Correspondence of a representation-model state with a registry-model vault: same
chain, same two maps, and — once the registry model has the tracked asset registered
— the same origin chain and origin token for it. -/
structure Corr (s : State Accounting) (thisChain : NativeTokenVault.Chain)
    (V : NativeTokenVault.Vault) : Prop where
  chain : thisChain = s.config.chainId
  registry : RegistryCorr s.registry V
  tracked : NativeTokenVault.Registered V s.config.assetId →
    V.originChain s.config.assetId = s.config.originChainId ∧
    V.originToken s.config.assetId = widen s.token.config.originToken

/-- The registry-model registration a representation-model registration corresponds
to: asset `config.assetId`, local token `config.tokenAddress`, origin token `origin`,
origin chain `config.originChainId`. -/
def correspondingRegistration (s : RegistrationState Accounting) (origin : Address)
    (V : NativeTokenVault.Vault) : NativeTokenVault.Vault :=
  NativeTokenVault.registerBridged V s.config.assetId (widen s.config.tokenAddress)
    (widen origin) s.config.originChainId

/-- The three conditions of the registry model's `RegisterBridgedGuard` that the
representation model's `registerFreshBranch` does not check, phrased on the
representation-model state. -/
structure RegistryOnlyGuards (s : RegistrationState Accounting) : Prop where
  /-- `RegisterBridgedGuard.tokenNonzero`. -/
  tokenNonzero : s.config.tokenAddress ≠ 0
  /-- `RegisterBridgedGuard.freshToken`. -/
  freshToken : s.registry.assetForToken s.config.tokenAddress = 0
  /-- `RegisterBridgedGuard.originNonzero`. -/
  originNonzero : s.config.originChainId ≠ 0

end Contracts.NativeTokenVaultBase
