import EraSpec.Contracts.NativeTokenVaultBase.Specs.ModelCorrespondence
import EraSpec.Contracts.NativeTokenVaultBase.Properties.Initialization
import EraSpec.Contracts.NativeTokenVaultBase.Properties.RepresentationPreparation

/-!
# Properties: how the two native-token-vault models relate

Statements about `EraSpec.Contracts.NativeTokenVaultBase.Specs.ModelCorrespondence`.
Proofs are in `EraSpec.Contracts.NativeTokenVaultBase.Proofs.ModelCorrespondence`.

## Where the models agree

* `RegistrationEffectCorresponds`: every successful representation-model
  registration writes, on corresponding states, exactly what the registry model's
  `registerBridged` writes to the overlapping maps.
* `RegistrationGuardGap`: on corresponding states, after a successful
  `registerFreshBranch`, the registry model's `RegisterBridgedGuard` holds **iff** the
  three `RegistryOnlyGuards` hold.  The other three registry guards follow from the
  representation model's own checks.
* `RegistrationIsRegistryStep` / `RegistrationPreservesValidOn`: with those three
  conditions, a representation-model registration is a registry-model `Step`, and the
  registry model's `Valid` (under its bounded hash premise) is carried through it.
* `PreparationIsForeignBridgeOut`: a successful `prepare`, on a state satisfying the
  representation model's own `RepresentationConsistent`, is a registry-model
  `bridgeOut` step on a non-native asset; that step leaves the vault unchanged, and
  the correspondence persists.
* `ValidRegistryHalvesAgree`: the registry model's `Valid` makes the two map
  directions of `RepresentationConsistent` equivalent, for nonzero entries.

## Where they disagree

The representation model admits registrations the registry model's guard rejects.
Each countermodel below is a successful `registerFreshBranch` on a state
corresponding to a `Valid` registry vault, with the bounded hash premise on a set
holding every pair that vault records and the new pair, whose post-state satisfies
the representation model's own `WellFormed` while the corresponding registry vault is
not `Valid`:

* `RepRegistrationRebindsLiveToken`: the deployed address is already some other
  asset's token (no `freshToken`);
* `RepRegistrationAcceptsZeroOriginChain`: origin chain `0` (no `originNonzero`);
* `RepRegistrationAcceptsZeroToken`: deployed address `0` (no `tokenNonzero`).

In the other direction, `RegistryBridgedAcceptsZeroOriginToken`: the registry model
registers a bridged asset with origin token `0`, which the representation model
never does.  Which model matches the source in each case is recorded in this
folder's README, not claimed by any statement here.

## Anti-vacuity

`CorrespondenceSatisfiable` meets every premise of `RegistrationPreservesValidOn`
(hence of `RegistrationEffectCorresponds`, `RegistrationGuardGap`,
`RegistrationIsRegistryStep`) on a vault that already holds a different asset.
`PreparationCorrespondenceSatisfiable` meets every premise of
`PreparationIsForeignBridgeOut` and `ValidRegistryHalvesAgree`, with `Valid` and the
representation model's `WellFormed` both holding.  `RegistrationGuardGap` is an iff;
`RepRegistrationRebindsLiveToken` exhibits its premises with both sides false, and
`CorrespondenceSatisfiable` with both true.
-/

namespace Contracts.NativeTokenVaultBase

open NativeTokenVault (Chain Vault World NtvAssetId Valid IdAssumptionsOn PairsIn
  RegisterBridgedGuard)

/-! ## Agreement on registration -/

/-- **THE REGISTRATION WRITES CORRESPOND.**  A successful representation-model
registration on a state corresponding to `V` yields a state corresponding to the
registry model's `registerBridged` of the same asset, token, origin token and origin
chain.  No guard of either model is assumed beyond the representation model's
success. -/
def Properties.RegistrationEffectCorresponds : Prop :=
  ∀ (Accounting : Type) (hooks : RegistrationHooks Accounting)
    (s : RegistrationState Accounting) (origin : Address) (out : Registered Accounting)
    (thisChain : Chain) (V : Vault),
    CorrPre s thisChain V → registerRepresentation hooks s origin = some out →
      Corr out.state thisChain (correspondingRegistration s origin V)

/-- **THE GUARD GAP, EXACTLY.**  On corresponding states, with the representation
model's asset encoder agreeing with the registry model's `e` at the one (chain,
token) pair the registration checks, a successful `registerFreshBranch` satisfies the
registry model's `RegisterBridgedGuard` if and only if `RegistryOnlyGuards` holds. -/
def Properties.RegistrationGuardGap : Prop :=
  ∀ (Accounting : Type) (hooks : RegistrationHooks Accounting)
    (s : RegistrationState Accounting) (origin : Address) (out : Registered Accounting)
    (e : NtvAssetId) (thisChain : Chain) (V : Vault),
    CorrPre s thisChain V → registerFreshBranch hooks s origin = some out →
    hooks.assetIdFor s.config.originChainId origin = e s.config.originChainId (widen origin) →
      (RegisterBridgedGuard e thisChain V s.config.assetId (widen s.config.tokenAddress)
          (widen origin) s.config.originChainId
        ↔ RegistryOnlyGuards s)

/-- **A GUARDED REPRESENTATION REGISTRATION IS A REGISTRY STEP.**  With the three
registry-only conditions, a successful `registerFreshBranch` on a state corresponding
to `W.vault` is a registry-model `Step` from `W`, to a world whose vault corresponds
to the representation model's post-state. -/
def Properties.RegistrationIsRegistryStep : Prop :=
  ∀ (Accounting : Type) (hooks : RegistrationHooks Accounting)
    (s : RegistrationState Accounting) (origin : Address) (out : Registered Accounting)
    (e : NtvAssetId) (thisChain : Chain) (W : World),
    CorrPre s thisChain W.vault → registerFreshBranch hooks s origin = some out →
    hooks.assetIdFor s.config.originChainId origin = e s.config.originChainId (widen origin) →
    RegistryOnlyGuards s →
      NativeTokenVault.Step e thisChain W
          { W with vault := correspondingRegistration s origin W.vault }
        ∧ Corr out.state thisChain (correspondingRegistration s origin W.vault)

/-- **THE REGISTRY INVARIANT IS CARRIED THROUGH A REPRESENTATION REGISTRATION.**  The
registry model's `Valid` and pair bound, under its bounded hash premise
`IdAssumptionsOn e S`, hold after a guarded representation-model registration on a
corresponding state whose (origin chain, origin token) pair is in `S`. -/
def Properties.RegistrationPreservesValidOn : Prop :=
  ∀ (Accounting : Type) (hooks : RegistrationHooks Accounting)
    (s : RegistrationState Accounting) (origin : Address) (out : Registered Accounting)
    (e : NtvAssetId) (S : Set (Chain × NativeTokenVault.Address)) (thisChain : Chain)
    (V : Vault),
    IdAssumptionsOn e S → thisChain ≠ 0 → Valid e thisChain V → PairsIn S V →
    (s.config.originChainId, widen origin) ∈ S →
    CorrPre s thisChain V → registerFreshBranch hooks s origin = some out →
    hooks.assetIdFor s.config.originChainId origin = e s.config.originChainId (widen origin) →
    RegistryOnlyGuards s →
      Valid e thisChain (correspondingRegistration s origin V)
        ∧ PairsIn S (correspondingRegistration s origin V)
        ∧ Corr out.state thisChain (correspondingRegistration s origin V)

/-! ## Agreement on the burn path -/

/-- **PREPARATION IS A FOREIGN `bridgeOut`.**  On a state satisfying the
representation model's `RepresentationConsistent` and corresponding to `W.vault`, a
successful `prepare` is a registry-model `bridgeOut` step of the request's asset and
amount towards its destination chain; the asset is not native in the registry model,
so that step leaves the vault unchanged, and the post-state still corresponds. -/
def Properties.PreparationIsForeignBridgeOut : Prop :=
  ∀ (Accounting : Type) (hooks : Hooks Accounting) (s : State Accounting) (r : Request)
    (out : Result Accounting) (e : NtvAssetId) (thisChain : Chain) (W : World),
    Corr s thisChain W.vault → RepresentationConsistent s → prepare hooks s r = some out →
      NativeTokenVault.Step e thisChain W
          (NativeTokenVault.bridgeOut thisChain W r.destinationChain r.assetId r.data.amount.val)
        ∧ ¬ NativeTokenVault.Native thisChain W.vault r.assetId
        ∧ (NativeTokenVault.bridgeOut thisChain W r.destinationChain r.assetId
            r.data.amount.val).vault = W.vault
        ∧ Corr out.state thisChain W.vault

/-! ## Agreement of the invariants -/

/-- **`Valid` MAKES THE TWO MAP DIRECTIONS AGREE.**  On a registry vault satisfying
`Valid` and corresponding to the representation maps `R`, for every asset `a` and
address `t`: `tokenForAsset a = t` with `t ≠ 0` iff `assetForToken t = a` with `a ≠ 0`.
So on such a state the last two conjuncts of `RepresentationConsistent` imply each
other, given nonzero entries. -/
def Properties.ValidRegistryHalvesAgree : Prop :=
  ∀ (e : NtvAssetId) (thisChain : Chain) (V : Vault) (R : Registry),
    Valid e thisChain V → RegistryCorr R V →
      ∀ (a : UInt256) (t : Address),
        (R.tokenForAsset a = t ∧ t ≠ 0) ↔ (R.assetForToken t = a ∧ a ≠ 0)

/-! ## Disagreements, as countermodels -/

/-- **THE REPRESENTATION MODEL CAN REBIND A LIVE TOKEN.**  A registry vault `V`
satisfying `Valid`, with the bounded hash premise on a set `S` holding every pair `V`
records and the new pair; a corresponding representation state whose configured
token address is nonzero and is already the token of a registered asset `b` other
than the one being registered; origin chain nonzero; and a successful
`registerFreshBranch`.  Its post-state is `WellFormed`.  The registry guard fails
(by `RegistrationGuardGap`, only `freshToken` can fail here).  In the corresponding
registry vault `b` still points at the token while the token points at the new asset,
and that vault is not `Valid`. -/
def Properties.RepRegistrationRebindsLiveToken : Prop :=
  ∃ (e : NtvAssetId) (S : Set (Chain × NativeTokenVault.Address)) (thisChain : Chain)
    (V : Vault) (hooks : RegistrationHooks Unit) (s : RegistrationState Unit)
    (origin : Address) (out : Registered Unit) (b : UInt256),
    IdAssumptionsOn e S ∧ thisChain ≠ 0 ∧ Valid e thisChain V ∧ PairsIn S V
    ∧ (s.config.originChainId, widen origin) ∈ S
    ∧ CorrPre s thisChain V ∧ registerFreshBranch hooks s origin = some out
    ∧ hooks.assetIdFor s.config.originChainId origin = e s.config.originChainId (widen origin)
    ∧ s.config.tokenAddress ≠ 0 ∧ s.config.originChainId ≠ 0
    ∧ b ≠ s.config.assetId ∧ NativeTokenVault.Registered V b
    ∧ V.token b = widen s.config.tokenAddress
    ∧ WellFormed out.state
    ∧ ¬ RegisterBridgedGuard e thisChain V s.config.assetId (widen s.config.tokenAddress)
          (widen origin) s.config.originChainId
    ∧ (correspondingRegistration s origin V).token b = widen s.config.tokenAddress
    ∧ (correspondingRegistration s origin V).assetOf (widen s.config.tokenAddress)
        = s.config.assetId
    ∧ ¬ Valid e thisChain (correspondingRegistration s origin V)

/-- **THE REPRESENTATION MODEL ACCEPTS ORIGIN CHAIN ZERO.**  As
`RepRegistrationRebindsLiveToken`'s premises, but with a token address that is
nonzero and unmapped, and origin chain `0`.  The corresponding registry vault has the
new asset registered with origin chain `0`, and is not `Valid`. -/
def Properties.RepRegistrationAcceptsZeroOriginChain : Prop :=
  ∃ (e : NtvAssetId) (S : Set (Chain × NativeTokenVault.Address)) (thisChain : Chain)
    (V : Vault) (hooks : RegistrationHooks Unit) (s : RegistrationState Unit)
    (origin : Address) (out : Registered Unit),
    IdAssumptionsOn e S ∧ thisChain ≠ 0 ∧ Valid e thisChain V ∧ PairsIn S V
    ∧ (s.config.originChainId, widen origin) ∈ S
    ∧ CorrPre s thisChain V ∧ registerFreshBranch hooks s origin = some out
    ∧ hooks.assetIdFor s.config.originChainId origin = e s.config.originChainId (widen origin)
    ∧ s.config.tokenAddress ≠ 0 ∧ s.registry.assetForToken s.config.tokenAddress = 0
    ∧ s.config.originChainId = 0
    ∧ WellFormed out.state
    ∧ NativeTokenVault.Registered (correspondingRegistration s origin V) s.config.assetId
    ∧ (correspondingRegistration s origin V).originChain s.config.assetId = 0
    ∧ ¬ Valid e thisChain (correspondingRegistration s origin V)

/-- **THE REPRESENTATION MODEL ACCEPTS DEPLOYED ADDRESS ZERO.**  As
`RepRegistrationRebindsLiveToken`'s premises, but with origin chain nonzero and the
configured token address `0`, so the successful registration deployed at `0`.  The
corresponding registry vault maps the zero address to the new, nonzero asset id, and
is not `Valid`. -/
def Properties.RepRegistrationAcceptsZeroToken : Prop :=
  ∃ (e : NtvAssetId) (S : Set (Chain × NativeTokenVault.Address)) (thisChain : Chain)
    (V : Vault) (hooks : RegistrationHooks Unit) (s : RegistrationState Unit)
    (origin : Address) (out : Registered Unit),
    IdAssumptionsOn e S ∧ thisChain ≠ 0 ∧ Valid e thisChain V ∧ PairsIn S V
    ∧ (s.config.originChainId, widen origin) ∈ S
    ∧ CorrPre s thisChain V ∧ registerFreshBranch hooks s origin = some out
    ∧ hooks.assetIdFor s.config.originChainId origin = e s.config.originChainId (widen origin)
    ∧ s.config.tokenAddress = 0 ∧ s.config.originChainId ≠ 0
    ∧ WellFormed out.state
    ∧ (correspondingRegistration s origin V).assetOf 0 = s.config.assetId
    ∧ s.config.assetId ≠ 0
    ∧ ¬ Valid e thisChain (correspondingRegistration s origin V)

/-- **THE REGISTRY MODEL ACCEPTS ORIGIN TOKEN ZERO; THE REPRESENTATION MODEL NEVER
DOES.**  There is a `Valid` registry vault, with the hash premise on the pair
involved, in which `RegisterBridgedGuard` holds for origin token `0` and the write
keeps the vault `Valid`.  And no representation-model registration succeeds with an
origin token that widens to `0`, for any hooks or state. -/
def Properties.RegistryBridgedAcceptsZeroOriginToken : Prop :=
  (∃ (e : NtvAssetId) (S : Set (Chain × NativeTokenVault.Address)) (thisChain : Chain)
      (V : Vault) (a : UInt256) (t : NativeTokenVault.Address) (originChain : Chain),
      IdAssumptionsOn e S ∧ thisChain ≠ 0 ∧ Valid e thisChain V ∧ PairsIn S V
      ∧ (originChain, 0) ∈ S
      ∧ RegisterBridgedGuard e thisChain V a t 0 originChain
      ∧ Valid e thisChain (NativeTokenVault.registerBridged V a t 0 originChain))
  ∧ ∀ (Accounting : Type) (hooks : RegistrationHooks Accounting)
      (s : RegistrationState Accounting) (origin : Address),
      widen origin = 0 → registerRepresentation hooks s origin = none

/-! ## Anti-vacuity -/

/-- **THE REGISTRATION PREMISES ARE SATISFIABLE, NONTRIVIALLY.**  Every premise of
`RegistrationPreservesValidOn`, on a registry vault that already holds an asset other
than the one being registered. -/
def Properties.CorrespondenceSatisfiable : Prop :=
  ∃ (e : NtvAssetId) (S : Set (Chain × NativeTokenVault.Address)) (thisChain : Chain)
    (V : Vault) (hooks : RegistrationHooks Unit) (s : RegistrationState Unit)
    (origin : Address) (out : Registered Unit),
    IdAssumptionsOn e S ∧ thisChain ≠ 0 ∧ Valid e thisChain V ∧ PairsIn S V
    ∧ (s.config.originChainId, widen origin) ∈ S
    ∧ CorrPre s thisChain V ∧ registerFreshBranch hooks s origin = some out
    ∧ hooks.assetIdFor s.config.originChainId origin = e s.config.originChainId (widen origin)
    ∧ RegistryOnlyGuards s
    ∧ ∃ b, b ≠ s.config.assetId ∧ NativeTokenVault.Registered V b

/-- **THE BURN-PATH PREMISES ARE SATISFIABLE.**  Every premise of
`PreparationIsForeignBridgeOut` and of `ValidRegistryHalvesAgree`, with the registry
vault `Valid`, the representation state `WellFormed`, and the tracked asset
registered. -/
def Properties.PreparationCorrespondenceSatisfiable : Prop :=
  ∃ (e : NtvAssetId) (thisChain : Chain) (W : World) (hooks : Hooks Unit) (s : State Unit)
    (r : Request) (out : Result Unit),
    Valid e thisChain W.vault ∧ Corr s thisChain W.vault ∧ WellFormed s
    ∧ s.registry.tokenForAsset s.config.assetId ≠ 0
    ∧ prepare hooks s r = some out

end Contracts.NativeTokenVaultBase
