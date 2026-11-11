import EraSpec.Contracts.NativeTokenVaultBase.Specs.RegistrationUnified
import EraSpec.Contracts.NativeTokenVaultBase.Properties.ModelCorrespondence

/-!
# Properties: the two vault models with the registration guard gap closed

Statements about `EraSpec.Contracts.NativeTokenVaultBase.Specs.RegistrationUnified`.
Proofs are in `EraSpec.Contracts.NativeTokenVaultBase.Proofs.RegistrationUnified`.

## The added guard is what the source supplies

* `TokenDataOriginChainIdZeroIff`: the normalised origin chain is `0` only if both the
  decoded field and `_l1ChainId()` are `0`.
* `SourceInputGivesRegistryOnlyGuards`: every successful ORIGINAL registration on a
  `SourceRegistrationInput` satisfies the three `RegistryOnlyGuards`.
* `UnifiedAgreesOnSourceInputs`: so on those inputs the tightened registration IS the
  original one; the added guard removes no source behaviour.
* `SourceInputPremisesLoadBearing`: each of the three premises behind that (nonzero
  `_l1ChainId()`, deployed address nonzero, deployed address unmapped) is needed.
* `UnifiedIsGuardedRestriction`: the tightened registration is the original one
  restricted to the three guards, exactly.

## (a) A tightened registration is a registry step, with no side condition

* `UnifiedRegistrationIsRegistryStep`: a successful `registerFreshBranch'` on a
  corresponding state satisfies the tightened registry guard `RegisterBridgedGuard'`,
  and is a tightened registry step `Step'` to a corresponding vault.  Unlike
  `RegistrationIsRegistryStep`, there is no `RegistryOnlyGuards` premise.
* `UnifiedRegistrationPreservesValidOn`: the registry invariant `Valid`, under the
  bounded hash premise `IdAssumptionsOn`, and the representation invariant `WellFormed`
  both hold after it.
* `UnifiedRegistrationGuardsAgree`: with the dependency results available (metadata
  decodes, the deployer returns the expected token, the tracker accepts), the
  tightened representation registration succeeds **iff** the tightened registry guard
  holds.  The original pair only had "succeeds → (guard ↔ `RegistryOnlyGuards`)".
* `TightStepIsStep`: the tightened registry model is a sub-model of the registry
  model, so every registry result about `Step` / `Reach` runs applies to it.
* `InnerRegistrationNeedsFreshSlot` (countermodel): without the caller's
  missing-forward-slot test, the inner registration can overwrite a registered asset
  and break `Valid`; that is why (a) is about `registerFreshBranch'`.

## (b) The four disagreements are gone

Each of the four countermodels of `Properties/ModelCorrespondence.lean` has no
instance once the primed definitions replace the unprimed ones.  The statements
below keep each countermodel's premise conjuncts and drop its conclusion conjuncts,
so they are stronger than the negation of the primed countermodel; they also
quantify over every accounting type, where the countermodels used `Unit`.

* `UnifiedRegistrationCannotRebindLiveToken` (against `RepRegistrationRebindsLiveToken`);
* `UnifiedRegistrationRejectsZeroOriginChain` (against
  `RepRegistrationAcceptsZeroOriginChain`);
* `UnifiedRegistrationRejectsZeroToken` (against `RepRegistrationAcceptsZeroToken`);
* `TightRegistryRejectsZeroOriginToken` (against `RegistryBridgedAcceptsZeroOriginToken`):
  the tightened registry guard rejects origin token `0`, and so does the tightened
  representation registration.

Along runs: `TightRunOriginTokensNonzero`, with no hash premise, no asset registered
on a tightened registry run has origin token `0`;
`RunCanRecordZeroOriginToken` shows an untightened bounded run that does, with
`Valid` holding.

## (c) The correspondence along the representation model's life

`LifecycleRelIsSimulation`: the relation `LifecycleRel` (correspondence, the
representation invariant, the tracked asset registered and not native, and the
supply/flow identity below) is a one-step forward simulation of the representation
model's `RepStep` by the registry model's flows, with no hash premise;
`RegistrationEstablishesLifecycleRel`: a tightened registration establishes it.  The
proof module packages the pair as a `LayeredVerification.Simulation`
(`Core/Simulation.lean`), `lifecycleSimulation`.

`UnifiedLifecycleCorresponds`: start from any bounded registry run from fresh storage
and a corresponding registration state.  A tightened registration, followed by ANY
run of preparations and token operations on the tracked token, is simulated by an
extension of that registry run: the registration is a `registerBridged` step, each
preparation and each nonzero token burn a `bridgeOut`, each mint a `bridgeIn`, and
transfers (and zero burns) no step.  At the end:

* the registry run is still a bounded run from fresh storage, and still a tightened
  run if its prefix was one;
* the registry vault is the one the registration wrote, unchanged since;
* `Corr` holds, `Valid` holds (for the run's own pair bound), and `WellFormed` holds;
* **the tracked token's total supply plus the asset's total recorded outflow equals
  its total recorded inflow.**  The registry model alone constrains its flow audit
  only for native assets (`LedgerIsNetFlowOn`); for this bridged asset the
  representation model's supply is the missing term, so in particular the run never
  records more outflow than inflow of it.

## Anti-vacuity

`SourceRegistrationInputSatisfiable` (with the decoded chain field `0`, so the
normalisation branch is taken), `UnifiedRegistrationSatisfiable` (every premise of
(a), on a vault that already holds another asset; both sides of the guard iff true),
`UnifiedGuardsAgreeBothFalse` (the iff's premises with both sides false, on a state
the ORIGINAL registration accepts), `TightRegistrySatisfiable` (a tightened run with
a native and a bridged registration), `LifecycleRelSatisfiable` (related states with a
supply-changing step) and `UnifiedLifecycleSatisfiable` (every premise of (c), with a
run that funds the token and then prepares a transfer).  The (b)
statements and `SourceInputPremisesLoadBearing`, `InnerRegistrationNeedsFreshSlot`,
`RunCanRecordZeroOriginToken` are negative results.
-/

namespace Contracts.NativeTokenVault

/-! ## The tightened registry model -/

/-- **THE TIGHTENED REGISTRY MODEL IS A SUB-MODEL.**  Every `Step'` is a `Step`, and
every `Reach'` run is a `Reach` run.  So every registry-model result about `Step` and
`Reach` (for instance `ReachIffReachLog`, hence `LoggedRunSound`) applies to the
tightened model. -/
def Properties.TightStepIsStep : Prop :=
  ∀ (e : NtvAssetId) (thisChain : Chain) (W X : World),
    (Step' e thisChain W X → Step e thisChain W X)
    ∧ (Reach' e thisChain W X → Reach e thisChain W X)

/-- **NO REGISTERED ASSET HAS ORIGIN TOKEN ZERO** at any point of a tightened run from
fresh storage.  There is no hash premise: a native registration records the token
itself (nonzero by `RegisterNativeGuard`), and a bridged one an origin token that
`RegisterBridgedGuard'` requires to be nonzero. -/
def Properties.TightRunOriginTokensNonzero : Prop :=
  ∀ (e : NtvAssetId) (thisChain : Chain) (W : World), Reach' e thisChain empty W →
    ∀ a, Registered W.vault a → W.vault.originToken a ≠ 0

/-- **THE UNTIGHTENED MODEL CAN.**  A bounded run of the registry model from fresh
storage, with the bounded hash premise on its pairs and a nonzero chain id, ends in a
`Valid` vault with a registered asset whose origin token is `0`.  So `Valid` does not
exclude it, and `TightRunOriginTokensNonzero` needs the tightened guard. -/
def Properties.RunCanRecordZeroOriginToken : Prop :=
  ∃ (e : NtvAssetId) (S : Set (Chain × Address)) (thisChain : Chain) (W : World),
    IdAssumptionsOn e S ∧ thisChain ≠ 0 ∧ ReachIn e thisChain S empty W
    ∧ Valid e thisChain W.vault
    ∧ ∃ a, Registered W.vault a ∧ W.vault.originToken a = 0

/-- **THE TIGHTENED MODEL'S PREMISES ARE SATISFIABLE, NONTRIVIALLY.**  A tightened run
from fresh storage, which is also a bounded run for a pair set with the bounded hash
premise, that registers a native asset and a bridged (non-native) asset.  Covers the
premises of `TightStepIsStep` and `TightRunOriginTokensNonzero`. -/
def Properties.TightRegistrySatisfiable : Prop :=
  ∃ (e : NtvAssetId) (S : Set (Chain × Address)) (thisChain : Chain) (W : World),
    IdAssumptionsOn e S ∧ thisChain ≠ 0 ∧ Reach' e thisChain empty W
    ∧ ReachIn e thisChain S empty W
    ∧ ∃ a b, a ≠ b ∧ Registered W.vault a ∧ Native thisChain W.vault a
      ∧ Registered W.vault b ∧ ¬ Native thisChain W.vault b

end Contracts.NativeTokenVault

namespace Contracts.NativeTokenVaultBase

open NativeTokenVault (Chain Vault World NtvAssetId Valid IdAssumptionsOn PairsIn
  RegisterBridgedGuard RegisterBridgedGuard')

/-! ## The added guard is what the source supplies -/

/-- **NORMALISATION.**  `tokenDataOriginChainId decoded l1ChainId` is `0` exactly when
the decoded field and `_l1ChainId()` are both `0`.  So with `_l1ChainId() ≠ 0` the
inner helper never sees origin chain `0`, whatever the sending chain put in the token
data. -/
def Properties.TokenDataOriginChainIdZeroIff : Prop :=
  ∀ decoded l1ChainId : UInt256,
    tokenDataOriginChainId decoded l1ChainId = 0 ↔ decoded = 0 ∧ l1ChainId = 0

/-- **THE SOURCE SUPPLIES THE THREE REGISTRY-ONLY CONDITIONS.**  A successful ORIGINAL
representation-model registration, on an input the source can produce (normalised
origin chain with a nonzero `_l1ChainId()`, fresh deployment), satisfies
`RegistryOnlyGuards`.  No hash premise. -/
def Properties.SourceInputGivesRegistryOnlyGuards : Prop :=
  ∀ (Accounting : Type) (hooks : RegistrationHooks Accounting)
    (s : RegistrationState Accounting) (origin : Address) (out : Registered Accounting)
    (decoded l1ChainId : UInt256),
    SourceRegistrationInput hooks s origin decoded l1ChainId →
    registerRepresentation hooks s origin = some out → RegistryOnlyGuards s

/-- **THE ADDED GUARD REMOVES NO SOURCE BEHAVIOUR.**  On an input the source can
produce, the tightened registration and fresh branch return exactly what the original
ones return, success or failure. -/
def Properties.UnifiedAgreesOnSourceInputs : Prop :=
  ∀ (Accounting : Type) (hooks : RegistrationHooks Accounting)
    (s : RegistrationState Accounting) (origin : Address) (decoded l1ChainId : UInt256),
    SourceRegistrationInput hooks s origin decoded l1ChainId →
      registerRepresentation' hooks s origin = registerRepresentation hooks s origin
      ∧ registerFreshBranch' hooks s origin = registerFreshBranch hooks s origin

/-- **EACH SOURCE-INPUT PREMISE IS NEEDED.**  Three successful ORIGINAL fresh-branch
registrations, each violating `RegistryOnlyGuards` while meeting the other parts of
`SourceRegistrationInput`:

1. `_l1ChainId() = 0` and the decoded field `0`, with a fresh deployment: origin chain
   `0`;
2. a nonzero `_l1ChainId()` and an unmapped deployed address, which is `0`;
3. a nonzero `_l1ChainId()` and a nonzero deployed address, which is already mapped. -/
def Properties.SourceInputPremisesLoadBearing : Prop :=
  (∃ (hooks : RegistrationHooks Unit) (s : RegistrationState Unit) (origin : Address)
      (out : Registered Unit),
      s.config.originChainId = tokenDataOriginChainId 0 0 ∧ DeployFresh hooks s origin
      ∧ registerFreshBranch hooks s origin = some out ∧ ¬ RegistryOnlyGuards s)
  ∧ (∃ (hooks : RegistrationHooks Unit) (s : RegistrationState Unit) (origin : Address)
      (out : Registered Unit) (decoded l1ChainId : UInt256),
      l1ChainId ≠ 0 ∧ s.config.originChainId = tokenDataOriginChainId decoded l1ChainId
      ∧ (∀ d, hooks.deploy s.config.originChainId origin = some d →
          s.registry.assetForToken d = 0)
      ∧ hooks.deploy s.config.originChainId origin = some 0
      ∧ registerFreshBranch hooks s origin = some out ∧ ¬ RegistryOnlyGuards s)
  ∧ (∃ (hooks : RegistrationHooks Unit) (s : RegistrationState Unit) (origin : Address)
      (out : Registered Unit) (decoded l1ChainId : UInt256),
      l1ChainId ≠ 0 ∧ s.config.originChainId = tokenDataOriginChainId decoded l1ChainId
      ∧ (∀ d, hooks.deploy s.config.originChainId origin = some d → d ≠ 0)
      ∧ registerFreshBranch hooks s origin = some out ∧ ¬ RegistryOnlyGuards s)

/-- **THE TIGHTENED REGISTRATION IS THE ORIGINAL ONE, GUARDED.**  Both the inner
registration and the fresh branch succeed with `out` iff the original one does and
`RegistryOnlyGuards` holds. -/
def Properties.UnifiedIsGuardedRestriction : Prop :=
  ∀ (Accounting : Type) (hooks : RegistrationHooks Accounting)
    (s : RegistrationState Accounting) (origin : Address) (out : Registered Accounting),
    (registerRepresentation' hooks s origin = some out ↔
      registerRepresentation hooks s origin = some out ∧ RegistryOnlyGuards s)
    ∧ (registerFreshBranch' hooks s origin = some out ↔
      registerFreshBranch hooks s origin = some out ∧ RegistryOnlyGuards s)

/-! ## (a) A tightened registration is a registry step, with no side condition -/

/-- **A TIGHTENED REGISTRATION IS A TIGHTENED REGISTRY STEP.**  On a registration state
corresponding to `W.vault`, with the representation model's asset encoder agreeing
with the registry model's `e` at the one (origin chain, origin token) pair checked, a
successful `registerFreshBranch'` satisfies `RegisterBridgedGuard'` for the
corresponding registry write, is a `Step'` from `W` to the world with that write, and
yields a state corresponding to it.  No `RegistryOnlyGuards` premise. -/
def Properties.UnifiedRegistrationIsRegistryStep : Prop :=
  ∀ (Accounting : Type) (hooks : RegistrationHooks Accounting)
    (s : RegistrationState Accounting) (origin : Address) (out : Registered Accounting)
    (e : NtvAssetId) (thisChain : Chain) (W : World),
    CorrPre s thisChain W.vault → registerFreshBranch' hooks s origin = some out →
    hooks.assetIdFor s.config.originChainId origin = e s.config.originChainId (widen origin) →
      RegisterBridgedGuard' e thisChain W.vault s.config.assetId (widen s.config.tokenAddress)
          (widen origin) s.config.originChainId
      ∧ NativeTokenVault.Step' e thisChain W
          { W with vault := correspondingRegistration s origin W.vault }
      ∧ Corr out.state thisChain (correspondingRegistration s origin W.vault)

/-- **BOTH INVARIANTS HOLD AFTER A TIGHTENED REGISTRATION.**  The registry model's
`Valid` and pair bound, under its bounded hash premise `IdAssumptionsOn e S` on a set
`S` holding the registered (origin chain, origin token) pair, hold for the
corresponding registry write; the correspondence holds; and the representation
model's `WellFormed` holds for its post-state.  No `RegistryOnlyGuards` premise. -/
def Properties.UnifiedRegistrationPreservesValidOn : Prop :=
  ∀ (Accounting : Type) (hooks : RegistrationHooks Accounting)
    (s : RegistrationState Accounting) (origin : Address) (out : Registered Accounting)
    (e : NtvAssetId) (S : Set (Chain × NativeTokenVault.Address)) (thisChain : Chain)
    (V : Vault),
    IdAssumptionsOn e S → thisChain ≠ 0 → Valid e thisChain V → PairsIn S V →
    (s.config.originChainId, widen origin) ∈ S →
    CorrPre s thisChain V → registerFreshBranch' hooks s origin = some out →
    hooks.assetIdFor s.config.originChainId origin = e s.config.originChainId (widen origin) →
      Valid e thisChain (correspondingRegistration s origin V)
        ∧ PairsIn S (correspondingRegistration s origin V)
        ∧ Corr out.state thisChain (correspondingRegistration s origin V)
        ∧ WellFormed out.state

/-- **THE TWO TIGHTENED GUARDS AGREE EXACTLY.**  On a registration state corresponding
to `V`, with the asset encoders agreeing at the checked pair, and with the three
dependency results the registration needs available (metadata decoding succeeds, the
deployer returns the expected token address, the tracker hook accepts the installed
registry and freshly initialized token), the tightened representation registration
succeeds iff `RegisterBridgedGuard'` holds for the corresponding registry write. -/
def Properties.UnifiedRegistrationGuardsAgree : Prop :=
  ∀ (Accounting : Type) (hooks : RegistrationHooks Accounting)
    (s : RegistrationState Accounting) (origin : Address) (accounting : Accounting)
    (e : NtvAssetId) (thisChain : Chain) (V : Vault),
    CorrPre s thisChain V →
    hooks.assetIdFor s.config.originChainId origin = e s.config.originChainId (widen origin) →
    hooks.metadataDecoded = true →
    hooks.deploy s.config.originChainId origin = some s.config.tokenAddress →
    hooks.registerTracker s.accounting
        (installRegistry s.registry s.config.assetId s.config.tokenAddress)
        (registeredToken s.config origin) s.config.assetId s.config.originChainId
      = some accounting →
      ((∃ out, registerFreshBranch' hooks s origin = some out) ↔
        RegisterBridgedGuard' e thisChain V s.config.assetId (widen s.config.tokenAddress)
          (widen origin) s.config.originChainId)

/-- **WHY (a) IS STATED FOR THE FRESH BRANCH.**  The tightened INNER registration
`registerRepresentation'` has no missing-forward-slot test, exactly as
`_ensureAndSaveTokenDeployedInner` has none.  It can succeed on a state corresponding to
a `Valid` vault, with every other premise of `UnifiedRegistrationPreservesValidOn`, whose
asset is already registered at another token; the registry guard then fails, and the
corresponding registry write breaks `Valid`.  In the source both callers test
`tokenAddress[_assetId] == address(0)` first (`NativeTokenVaultBase.sol:253`, `:301`),
which is `registerFreshBranch'`'s test. -/
def Properties.InnerRegistrationNeedsFreshSlot : Prop :=
  ∃ (e : NtvAssetId) (S : Set (Chain × NativeTokenVault.Address)) (thisChain : Chain)
    (V : Vault) (hooks : RegistrationHooks Unit) (s : RegistrationState Unit)
    (origin : Address) (out : Registered Unit),
    IdAssumptionsOn e S ∧ thisChain ≠ 0 ∧ Valid e thisChain V ∧ PairsIn S V
    ∧ (s.config.originChainId, widen origin) ∈ S
    ∧ CorrPre s thisChain V ∧ registerRepresentation' hooks s origin = some out
    ∧ hooks.assetIdFor s.config.originChainId origin = e s.config.originChainId (widen origin)
    ∧ s.registry.tokenForAsset s.config.assetId ≠ 0
    ∧ ¬ RegisterBridgedGuard e thisChain V s.config.assetId (widen s.config.tokenAddress)
        (widen origin) s.config.originChainId
    ∧ ¬ Valid e thisChain (correspondingRegistration s origin V)

/-! ## (b) The four disagreements are gone -/

/-- **NO TIGHTENED REGISTRATION REBINDS A LIVE TOKEN.**  `RepRegistrationRebindsLiveToken`'s
premises, with `registerFreshBranch'`, have no instance: on a `Valid` corresponding
vault, a successful tightened registration never deploys at the token of another
registered asset. -/
def Properties.UnifiedRegistrationCannotRebindLiveToken : Prop :=
  ∀ Accounting : Type, ¬ ∃ (e : NtvAssetId) (S : Set (Chain × NativeTokenVault.Address))
    (thisChain : Chain) (V : Vault) (hooks : RegistrationHooks Accounting)
    (s : RegistrationState Accounting) (origin : Address) (out : Registered Accounting)
    (b : UInt256),
    IdAssumptionsOn e S ∧ thisChain ≠ 0 ∧ Valid e thisChain V ∧ PairsIn S V
    ∧ (s.config.originChainId, widen origin) ∈ S
    ∧ CorrPre s thisChain V ∧ registerFreshBranch' hooks s origin = some out
    ∧ hooks.assetIdFor s.config.originChainId origin = e s.config.originChainId (widen origin)
    ∧ s.config.tokenAddress ≠ 0 ∧ s.config.originChainId ≠ 0
    ∧ b ≠ s.config.assetId ∧ NativeTokenVault.Registered V b
    ∧ V.token b = widen s.config.tokenAddress

/-- **NO TIGHTENED REGISTRATION HAS ORIGIN CHAIN ZERO.**
`RepRegistrationAcceptsZeroOriginChain`'s premises, with `registerFreshBranch'`, have no
instance. -/
def Properties.UnifiedRegistrationRejectsZeroOriginChain : Prop :=
  ∀ Accounting : Type, ¬ ∃ (e : NtvAssetId) (S : Set (Chain × NativeTokenVault.Address))
    (thisChain : Chain) (V : Vault) (hooks : RegistrationHooks Accounting)
    (s : RegistrationState Accounting) (origin : Address) (out : Registered Accounting),
    IdAssumptionsOn e S ∧ thisChain ≠ 0 ∧ Valid e thisChain V ∧ PairsIn S V
    ∧ (s.config.originChainId, widen origin) ∈ S
    ∧ CorrPre s thisChain V ∧ registerFreshBranch' hooks s origin = some out
    ∧ hooks.assetIdFor s.config.originChainId origin = e s.config.originChainId (widen origin)
    ∧ s.config.tokenAddress ≠ 0 ∧ s.registry.assetForToken s.config.tokenAddress = 0
    ∧ s.config.originChainId = 0

/-- **NO TIGHTENED REGISTRATION DEPLOYS AT ADDRESS ZERO.**
`RepRegistrationAcceptsZeroToken`'s premises, with `registerFreshBranch'`, have no
instance. -/
def Properties.UnifiedRegistrationRejectsZeroToken : Prop :=
  ∀ Accounting : Type, ¬ ∃ (e : NtvAssetId) (S : Set (Chain × NativeTokenVault.Address))
    (thisChain : Chain) (V : Vault) (hooks : RegistrationHooks Accounting)
    (s : RegistrationState Accounting) (origin : Address) (out : Registered Accounting),
    IdAssumptionsOn e S ∧ thisChain ≠ 0 ∧ Valid e thisChain V ∧ PairsIn S V
    ∧ (s.config.originChainId, widen origin) ∈ S
    ∧ CorrPre s thisChain V ∧ registerFreshBranch' hooks s origin = some out
    ∧ hooks.assetIdFor s.config.originChainId origin = e s.config.originChainId (widen origin)
    ∧ s.config.tokenAddress = 0 ∧ s.config.originChainId ≠ 0

/-- **NEITHER TIGHTENED MODEL REGISTERS ORIGIN TOKEN ZERO.**
`RegistryBridgedAcceptsZeroOriginToken`'s registry-side premises, with
`RegisterBridgedGuard'`, have no instance; and, as before, no tightened representation
registration succeeds with an origin token that widens to `0`. -/
def Properties.TightRegistryRejectsZeroOriginToken : Prop :=
  (¬ ∃ (e : NtvAssetId) (S : Set (Chain × NativeTokenVault.Address)) (thisChain : Chain)
      (V : Vault) (a : UInt256) (t : NativeTokenVault.Address) (originChain : Chain),
      IdAssumptionsOn e S ∧ thisChain ≠ 0 ∧ Valid e thisChain V ∧ PairsIn S V
      ∧ (originChain, 0) ∈ S
      ∧ RegisterBridgedGuard' e thisChain V a t 0 originChain)
  ∧ ∀ (Accounting : Type) (hooks : RegistrationHooks Accounting)
      (s : RegistrationState Accounting) (origin : Address),
      widen origin = 0 → registerRepresentation' hooks s origin = none

/-! ## (c) The correspondence along the representation model's life -/

/-- **ONE STEP OF THE SIMULATION.**  From states related by `LifecycleRel`, each
representation-model step is matched either by no registry step or by one step that
is both a bounded step (`StepIn`, for any pair set: the matched steps are flows,
which hash nothing) and a tightened step (`Step'`).  The registry vault is unchanged,
the representation model's configuration is kept, and the relation persists.  No
hash premise. -/
def Properties.LifecycleRelIsSimulation : Prop :=
  ∀ (Accounting : Type) (hooks : Hooks Accounting) (e : NtvAssetId)
    (S : Set (Chain × NativeTokenVault.Address)) (thisChain : Chain)
    (u u' : State Accounting) (W : World),
    LifecycleRel thisChain u W → RepStep hooks u u' →
      ∃ W' : World,
        (W' = W ∨ (NativeTokenVault.StepIn e thisChain S W W'
          ∧ NativeTokenVault.Step' e thisChain W W'))
        ∧ W'.vault = W.vault ∧ u'.config = u.config ∧ LifecycleRel thisChain u' W'

/-- **A TIGHTENED REGISTRATION ESTABLISHES THE RELATION.**  After a bounded registry run
from fresh storage (under the bounded hash premise on its pair set, with a nonzero
chain id), a successful tightened registration on a corresponding state, with the
asset encoders agreeing at the registered pair, relates the registered state to the
world carrying the corresponding registry write.  (The recorded flows of the new asset
are zero because the registry audit records none for an unregistered asset.) -/
def Properties.RegistrationEstablishesLifecycleRel : Prop :=
  ∀ (Accounting : Type) (rhooks : RegistrationHooks Accounting)
    (s : RegistrationState Accounting) (origin : Address) (reg : Registered Accounting)
    (e : NtvAssetId) (S : Set (Chain × NativeTokenVault.Address)) (thisChain : Chain)
    (W : World),
    IdAssumptionsOn e S → thisChain ≠ 0 →
    NativeTokenVault.ReachIn e thisChain S NativeTokenVault.empty W →
    CorrPre s thisChain W.vault → registerFreshBranch' rhooks s origin = some reg →
    rhooks.assetIdFor s.config.originChainId origin = e s.config.originChainId (widen origin) →
      LifecycleRel thisChain reg.state
        { W with vault := correspondingRegistration s origin W.vault }

/-- **THE REPRESENTATION MODEL'S LIFE IS A REGISTRY RUN.**  Premises: a bounded registry
run from fresh storage to `W`, under the bounded hash premise on its pair set `S`,
with a nonzero chain id; a registration state corresponding to `W.vault` whose
(origin chain, origin token) pair is in `S`; a successful tightened registration with
the asset encoders agreeing at that pair; and any run of preparations and token
operations from the registered state to `t`.

Conclusion: some extension `W'` of the registry run is still a bounded run from fresh
storage, and still a tightened run if the prefix was one; its vault is the
registration's write, unchanged since; `t` corresponds to it; both models' invariants
hold; and the tracked token's total supply plus the asset's total recorded outflow
equals its total recorded inflow. -/
def Properties.UnifiedLifecycleCorresponds : Prop :=
  ∀ (Accounting : Type) (rhooks : RegistrationHooks Accounting) (hooks : Hooks Accounting)
    (s : RegistrationState Accounting) (origin : Address) (reg : Registered Accounting)
    (t : State Accounting) (e : NtvAssetId) (S : Set (Chain × NativeTokenVault.Address))
    (thisChain : Chain) (W : World),
    IdAssumptionsOn e S → thisChain ≠ 0 →
    NativeTokenVault.ReachIn e thisChain S NativeTokenVault.empty W →
    (s.config.originChainId, widen origin) ∈ S →
    CorrPre s thisChain W.vault → registerFreshBranch' rhooks s origin = some reg →
    rhooks.assetIdFor s.config.originChainId origin = e s.config.originChainId (widen origin) →
    RepReach hooks reg.state t →
      ∃ W' : World,
        NativeTokenVault.ReachIn e thisChain S NativeTokenVault.empty W'
        ∧ (NativeTokenVault.Reach' e thisChain NativeTokenVault.empty W →
            NativeTokenVault.Reach' e thisChain NativeTokenVault.empty W')
        ∧ W'.vault = correspondingRegistration s origin W.vault
        ∧ Corr t thisChain W'.vault ∧ Valid e thisChain W'.vault ∧ WellFormed t
        ∧ t.token.totalSupply + W'.audit.totalOut s.config.assetId
            = W'.audit.totalIn s.config.assetId

/-! ## Anti-vacuity -/

/-- **THE SOURCE-INPUT PREMISE IS SATISFIABLE**, with the decoded chain field `0`, so
the origin chain comes from `_l1ChainId()`, and with a registration that succeeds in
both the original and the tightened fresh branch.  Covers the premises of
`SourceInputGivesRegistryOnlyGuards` and `UnifiedAgreesOnSourceInputs`. -/
def Properties.SourceRegistrationInputSatisfiable : Prop :=
  ∃ (hooks : RegistrationHooks Unit) (s : RegistrationState Unit) (origin : Address)
    (out : Registered Unit) (decoded l1ChainId : UInt256),
    SourceRegistrationInput hooks s origin decoded l1ChainId ∧ decoded = 0
    ∧ registerRepresentation hooks s origin = some out
    ∧ registerFreshBranch hooks s origin = some out
    ∧ registerFreshBranch' hooks s origin = some out

/-- **THE (a) PREMISES ARE SATISFIABLE, NONTRIVIALLY.**  Every premise of
`UnifiedRegistrationIsRegistryStep`, `UnifiedRegistrationPreservesValidOn` and
`UnifiedRegistrationGuardsAgree`, with the tightened registration succeeding (so both
sides of the iff hold), on a `Valid` vault that already holds an asset other than the
one being registered. -/
def Properties.UnifiedRegistrationSatisfiable : Prop :=
  ∃ (e : NtvAssetId) (S : Set (Chain × NativeTokenVault.Address)) (thisChain : Chain)
    (V : Vault) (hooks : RegistrationHooks Unit) (s : RegistrationState Unit)
    (origin : Address) (out : Registered Unit),
    IdAssumptionsOn e S ∧ thisChain ≠ 0 ∧ Valid e thisChain V ∧ PairsIn S V
    ∧ (s.config.originChainId, widen origin) ∈ S
    ∧ CorrPre s thisChain V ∧ registerFreshBranch' hooks s origin = some out
    ∧ hooks.assetIdFor s.config.originChainId origin = e s.config.originChainId (widen origin)
    ∧ hooks.metadataDecoded = true
    ∧ hooks.deploy s.config.originChainId origin = some s.config.tokenAddress
    ∧ hooks.registerTracker s.accounting
        (installRegistry s.registry s.config.assetId s.config.tokenAddress)
        (registeredToken s.config origin) s.config.assetId s.config.originChainId = some ()
    ∧ ∃ b, b ≠ s.config.assetId ∧ NativeTokenVault.Registered V b

/-- **THE GUARD IFF IS NOT ONE-SIDED.**  Every premise of
`UnifiedRegistrationGuardsAgree`, with both sides false — on a state where the
ORIGINAL fresh-branch registration succeeds (the deployed address is another asset's
token). -/
def Properties.UnifiedGuardsAgreeBothFalse : Prop :=
  ∃ (e : NtvAssetId) (thisChain : Chain) (V : Vault) (hooks : RegistrationHooks Unit)
    (s : RegistrationState Unit) (origin : Address),
    CorrPre s thisChain V
    ∧ hooks.assetIdFor s.config.originChainId origin = e s.config.originChainId (widen origin)
    ∧ hooks.metadataDecoded = true
    ∧ hooks.deploy s.config.originChainId origin = some s.config.tokenAddress
    ∧ hooks.registerTracker s.accounting
        (installRegistry s.registry s.config.assetId s.config.tokenAddress)
        (registeredToken s.config origin) s.config.assetId s.config.originChainId = some ()
    ∧ registerFreshBranch' hooks s origin = none
    ∧ ¬ RegisterBridgedGuard' e thisChain V s.config.assetId (widen s.config.tokenAddress)
        (widen origin) s.config.originChainId
    ∧ ∃ out, registerFreshBranch hooks s origin = some out

/-- **THE STEP-SIMULATION PREMISES ARE SATISFIABLE, NONTRIVIALLY.**  Related states and
a representation-model step from them that changes the token's supply.  Covers the
premises of `LifecycleRelIsSimulation`; those of `RegistrationEstablishesLifecycleRel`
are covered by `UnifiedLifecycleSatisfiable`. -/
def Properties.LifecycleRelSatisfiable : Prop :=
  ∃ (hooks : Hooks Unit) (thisChain : Chain) (u u' : State Unit) (W : World),
    LifecycleRel thisChain u W ∧ RepStep hooks u u'
    ∧ u'.token.totalSupply ≠ u.token.totalSupply

/-- **THE (c) PREMISES ARE SATISFIABLE, NONTRIVIALLY.**  Every premise of
`UnifiedLifecycleCorresponds` (hence of `RegistrationEstablishesLifecycleRel`), with a
registry prefix that registers an asset, and a run that first gives the token a
nonzero supply and then performs a successful preparation, ending in `t`. -/
def Properties.UnifiedLifecycleSatisfiable : Prop :=
  ∃ (rhooks : RegistrationHooks Unit) (hooks : Hooks Unit) (s : RegistrationState Unit)
    (origin : Address) (reg : Registered Unit) (t : State Unit) (e : NtvAssetId)
    (S : Set (Chain × NativeTokenVault.Address)) (thisChain : Chain) (W : World),
    IdAssumptionsOn e S ∧ thisChain ≠ 0
    ∧ NativeTokenVault.ReachIn e thisChain S NativeTokenVault.empty W
    ∧ (s.config.originChainId, widen origin) ∈ S
    ∧ CorrPre s thisChain W.vault ∧ registerFreshBranch' rhooks s origin = some reg
    ∧ rhooks.assetIdFor s.config.originChainId origin = e s.config.originChainId (widen origin)
    ∧ RepReach hooks reg.state t
    ∧ (∃ b, NativeTokenVault.Registered W.vault b)
    ∧ ∃ (mid : State Unit) (r : Request) (out : Result Unit),
        RepReach hooks reg.state mid ∧ mid.token.totalSupply ≠ 0
        ∧ prepare hooks mid r = some out ∧ t = out.state

end Contracts.NativeTokenVaultBase
