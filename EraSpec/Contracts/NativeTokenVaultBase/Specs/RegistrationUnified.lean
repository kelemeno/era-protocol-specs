import EraSpec.Contracts.NativeTokenVaultBase.Specs.ModelCorrespondence

/-!
# The two vault models, with the registration guard gap closed

`Specs/ModelCorrespondence.lean` relates the representation model's registration
(`registerFreshBranch`, namespace `Contracts.NativeTokenVaultBase`) to the registry
model's `registerBridged` (namespace `Contracts.NativeTokenVault`).  Its properties
find four disagreements: the representation model registers at an already-mapped
token address, at token address `0`, and with origin chain `0`, all of which the
registry model's `RegisterBridgedGuard` rejects; and the registry model registers
origin token `0`, which the representation model never does.  Each model lacks a
condition the source implies.

This file adds each missing condition to the model that lacks it, as a NEW
definition beside the unchanged original (era-contracts `c67894b9`, paths relative
to `l1-contracts/contracts/` unless they start with `system-contracts/`):

| Added to | Condition | Where the source gets it |
|---|---|---|
| `registerRepresentation'` | origin chain `≠ 0` | `tokenDataOriginChainId` replaces a decoded `0` by `_l1ChainId()` (`bridge/ntv/NativeTokenVaultBase.sol:565-571`) and the result is the inner helper's `_tokenOriginChainId` (`:544-551`); it is nonzero when `_l1ChainId() ≠ 0` |
| `registerRepresentation'` | token address `≠ 0` | the token address is checked against the address the CREATE2 deployment returned (`:582-583`), which is never `0`: L1 `Create2.deploy` (`bridge/ntv/L1NativeTokenVault.sol:249-257`), L2 `ContractDeployer` refuses kernel-space addresses (`system-contracts/contracts/ContractDeployer.sol:434-436`) |
| `registerRepresentation'` | token address unmapped | the same deployment reverts at an occupied address (`ContractDeployer.sol:438-446`; a CREATE2 collision on L1), and a mapped token address is occupied |
| `RegisterBridgedGuard'` | origin token `≠ 0` | `bridgeInitialize` requires `_originToken != address(0)` (`bridge/BridgedStandardERC20.sol:86`); `_deployBridgedToken` calls it (`NativeTokenVaultBase.sol:630`) before the registry write (`:585`) |

The source has no `require` for the first three.  They follow from mechanisms the
representation model takes as parameters: the resolved origin chain
`config.originChainId`, and the `deploy` hook.  So they appear twice here:

* as an explicit guard of `registerRepresentation'` (the three `RegistryOnlyGuards`
  of `Specs/ModelCorrespondence.lean`), which makes the representation model's
  registration agree with the registry model's on its own inputs; and
* as properties of the inputs the source can produce (`SourceRegistrationInput`).
  `Properties.UnifiedAgreesOnSourceInputs` shows the guard never fires on such
  inputs, so it removes no source behaviour.  The deployment facts are `VM-DEPLOY`,
  and stay premises (`DeployFresh`).

The tightened registry model is `Step'` / `Reach'`: the registry model's `Step` with
`RegisterBridgedGuard'` on the bridged registration, and every other operation as
before.

## The representation model after registration

`RepStep` / `RepReach` is the life of the tracked token after its registration: a
`prepare` (the `bridgeBurn` branch), or one operation of the token model on it (the
vault's `bridgeMint` / `bridgeBurn`, or an ordinary transfer).
`Properties.UnifiedLifecycleCorresponds` simulates it by registry-model runs.

## Model boundaries

Unchanged from `Specs/ModelCorrespondence.lean`.  In addition: `DeployFresh` is a
premise about one deployment call, not a model of code storage, so the step from
"occupied addresses make CREATE2 revert" to "mapped addresses are not returned"
(every mapped token address carries code) is part of the premise.  On L2,
`_l1ChainId()` is whatever `updateL2` stored, which it does not check for zero
(`bridge/ntv/L2NativeTokenVault.sol:160-164`); `SourceRegistrationInput.l1Nonzero`
is configuration there (`OPS-CONFIG`).

**This file is definitions only.**  Statements are in
`EraSpec.Contracts.NativeTokenVaultBase.Properties.RegistrationUnified`.
-/

namespace Contracts.NativeTokenVault

/-! ## The tightened registry model -/

/-- `RegisterBridgedGuard`, plus the origin-token check the source performs on this
path before the registry write: `_deployBridgedToken` (`NativeTokenVaultBase.sol:630`)
calls `bridgeInitialize`, which requires `_originToken != address(0)`
(`BridgedStandardERC20.sol:86`), and only then does `_ensureAndSaveTokenDeployedInner`
write the registry (`NativeTokenVaultBase.sol:585`). -/
structure RegisterBridgedGuard' (e : NtvAssetId) (thisChain : Chain) (V : Vault)
    (a : AssetId) (t ot : Address) (origin : Chain) : Prop
    extends RegisterBridgedGuard e thisChain V a t ot origin where
  /-- `require(_originToken != address(0), ZeroAddress())`. -/
  originTokenNonzero : ot ≠ 0

/-- The registry model's `Step`, with `RegisterBridgedGuard'` on the bridged
registration.  Every other operation is unchanged. -/
inductive Step' (e : NtvAssetId) (thisChain : Chain) : World → World → Prop
  | registerNative {W t} : RegisterNativeGuard W.vault t →
      Step' e thisChain W { W with vault := registerNative e thisChain W.vault t }
  | registerBridged {W a t ot origin} :
      RegisterBridgedGuard' e thisChain W.vault a t ot origin →
      Step' e thisChain W { W with vault := registerBridged W.vault a t ot origin }
  | bridgeOut {W c a amt} : FlowOutGuard W.vault a amt →
      Step' e thisChain W (bridgeOut thisChain W c a amt)
  | bridgeIn {W c a amt} : FlowInGuard thisChain W.vault a amt →
      Step' e thisChain W (bridgeIn thisChain W c a amt)
  | donate {W a amt} : Step' e thisChain W (donate W a amt)

/-- Reachability through `Step'`. -/
inductive Reach' (e : NtvAssetId) (thisChain : Chain) : World → World → Prop
  | refl {W} : Reach' e thisChain W W
  | tail {W X Y} : Reach' e thisChain W X → Step' e thisChain X Y → Reach' e thisChain W Y

end Contracts.NativeTokenVault

namespace Contracts.NativeTokenVaultBase

variable {Accounting : Type}

/-! ## Where the three registry-only conditions come from -/

/-- `tokenDataOriginChainId` (`NativeTokenVaultBase.sol:565-571`), taking the chain-id
field `decoded` that `DataEncoding.decodeTokenData` returns (`DataEncoding.sol:174-186`)
and the vault's `_l1ChainId()`: a decoded `0` stands for L1.  The decoded field comes
from the mint data, which the sending chain supplies. -/
def tokenDataOriginChainId (decoded l1ChainId : UInt256) : UInt256 :=
  if decoded = 0 then l1ChainId else decoded

/-- **`VM-DEPLOY`, for one registration call.**  Every address the deploy dependency
can return for this call's (origin chain, origin token) is nonzero and carries no
asset id in the registry about to be written.

The source discharges this from the deployment mechanism, not from a check of its
own:

* nonzero: L1 deploys with OpenZeppelin `Create2.deploy`
  (`L1NativeTokenVault.sol:249-257`), which reverts when CREATE2 returns `0`; L2
  deploys through the `ContractDeployer` system contract
  (`L2NativeTokenVault.sol:217-236`), which reverts for any address up to
  `MAX_SYSTEM_CONTRACT_ADDRESS` (`system-contracts/contracts/ContractDeployer.sol:434-436`);
* unmapped: both revert at an occupied address (`ContractDeployer.sol:438-446`;
  CREATE2 fails on a collision on L1), and every address with `assetId[t] ≠ 0` is
  occupied: a native token had code when registered (`NativeTokenVaultBase.sol:139`),
  a bridged one was deployed here, and the L2 base token is a system contract.  The
  last step is a fact about code storage, which no model here has, so it is part of
  this premise. -/
structure DeployFresh (hooks : RegistrationHooks Accounting) (s : RegistrationState Accounting)
    (origin : Address) : Prop where
  nonzero : ∀ d, hooks.deploy s.config.originChainId origin = some d → d ≠ 0
  unmapped : ∀ d, hooks.deploy s.config.originChainId origin = some d →
    s.registry.assetForToken d = 0

/-- **The inputs the source's registration path can produce.**  The registration
state's origin chain is what `tokenDataOriginChainId` resolves from the decoded field
`decoded` and the vault's nonzero `l1ChainId`, and the deploy dependency is fresh. -/
structure SourceRegistrationInput (hooks : RegistrationHooks Accounting)
    (s : RegistrationState Accounting) (origin : Address) (decoded l1ChainId : UInt256) :
    Prop where
  /-- `_l1ChainId() ≠ 0`.  On L1 it is the deployment's `block.chainid`
  (`L1NativeTokenVault.sol:120`).  On L2 it is the value `updateL2` stored
  (`L2NativeTokenVault.sol:160-164`), which is not checked for zero: configuration. -/
  l1Nonzero : l1ChainId ≠ 0
  /-- The origin chain handed to the inner helper is the normalised one
  (`NativeTokenVaultBase.sol:544-551`, `L2NativeTokenVault.sol:200-208`). -/
  originChain : s.config.originChainId = tokenDataOriginChainId decoded l1ChainId
  /-- The deployment law. -/
  deployFresh : DeployFresh hooks s origin

/-! ## The tightened representation-model registration -/

/-- The three `RegistryOnlyGuards` are decidable: they are equalities of words. -/
instance (s : RegistrationState Accounting) : Decidable (RegistryOnlyGuards s) :=
  decidable_of_iff (s.config.tokenAddress ≠ 0 ∧
      s.registry.assetForToken s.config.tokenAddress = 0 ∧ s.config.originChainId ≠ 0)
    ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩

/-- `registerRepresentation`, with the three `RegistryOnlyGuards` (token address
nonzero, token address not yet mapped, origin chain nonzero) checked first.  Failure
is `none` whichever check fails, so their order relative to the other checks does
not matter.  The table in this file's header gives the source mechanism behind each;
`Properties.UnifiedAgreesOnSourceInputs` shows they never fail on inputs satisfying
`SourceRegistrationInput`. -/
def registerRepresentation' (hooks : RegistrationHooks Accounting)
    (s : RegistrationState Accounting) (origin : Address) : Option (Registered Accounting) :=
  if RegistryOnlyGuards s then registerRepresentation hooks s origin else none

/-- `registerFreshBranch` with the tightened registration: the caller's
missing-forward-slot test (`token == address(0)`, `NativeTokenVaultBase.sol:253`,
`:301`), then `registerRepresentation'`. -/
def registerFreshBranch' (hooks : RegistrationHooks Accounting)
    (s : RegistrationState Accounting) (origin : Address) : Option (Registered Accounting) :=
  if s.registry.tokenForAsset s.config.assetId = 0 then registerRepresentation' hooks s origin
  else none

/-! ## The representation model after registration -/

/-- **One operation on the tracked token after its registration**: the `bridgeBurn`
branch (`prepare`), or one operation of the token model on the tracked token — the
vault's `bridgeMint` / `bridgeBurn` (`BridgedStandardERC20.sol:170-182`), or an
ordinary transfer.  The token model's mint and burn require the caller to be the
token's configured vault. -/
inductive RepStep (hooks : Hooks Accounting) : State Accounting → State Accounting → Prop
  /-- A successful `prepare`. -/
  | prepared {s : State Accounting} {r : Request} {out : Result Accounting} :
      prepare hooks s r = some out → RepStep hooks s out.state
  /-- A successful token-model operation on the tracked token. -/
  | tokenOp {s : State Accounting} {t : BridgedStandardERC20.State} :
      BridgedStandardERC20.Step s.token t → RepStep hooks s { s with token := t }

/-- Reachability through `RepStep`. -/
inductive RepReach (hooks : Hooks Accounting) : State Accounting → State Accounting → Prop
  | refl {s} : RepReach hooks s s
  | tail {s t u} : RepReach hooks s t → RepStep hooks t u → RepReach hooks s u

end Contracts.NativeTokenVaultBase
