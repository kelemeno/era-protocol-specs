import EraSpec.Contracts.NativeTokenVaultBase.Specs.RegistrationUnifiedStrong
import EraSpec.Contracts.NativeTokenVaultBase.Properties.RegistrationUnified

/-!
# Properties: the lifecycle correspondence, tied to the logged run

Statements about `EraSpec.Contracts.NativeTokenVaultBase.Specs.RegistrationUnifiedStrong`.
Proofs are in `EraSpec.Contracts.NativeTokenVaultBase.Proofs.RegistrationUnifiedStrong`.

## Why `UnifiedLifecycleCorresponds` needs a stronger form

`Properties.UnifiedLifecycleCorresponds` (`Properties/RegistrationUnified.lean`)
concludes that SOME registry world `W'` satisfies a list of conjuncts, the last being
"the tracked token's total supply plus the asset's recorded outflow equals its recorded
inflow".  Nothing in the statement ties `W'` to the run from the registered state to
`t`.  For a registered asset that is not native here, the registry's flow guards ask
only that it be registered and, on the way out, that the amount be nonzero, and such a
flow leaves the vault alone.  So from any `W'` meeting the other conjuncts, one more
bounded, tightened flow step meets them too and makes the identity hold for any number
in place of the supply.

* `UnifiedLifecycleSupplyConjunctFree`: under the premises of
  `UnifiedLifecycleCorresponds`, its conclusion holds with ANY `n : ℕ` in place of
  `t.token.totalSupply`.  So the identity conjunct, as stated there, carries no
  information about the run.

## The trace-tied form

* `LifecycleRepReachIffReachLog`: `RepReach` and the logged `LifecycleReachLog` have the
  same runs, so the logged statements below cover every run of the unlogged ones.
* `LifecycleLoggedSupply`: along a logged run from a `WellFormed` state, `WellFormed`
  and the configuration are kept, and the token's supply plus everything prepared or
  burned equals the starting supply plus everything minted.  No registry model.
* `UnifiedLifecycleTraced`: the premises of `UnifiedLifecycleCorresponds`, with the run
  logged.  Let `W₁` be the world the registration writes and `L` the matched registry
  log `lifecycleRegistryLog a c trace` of the logged run (for the tracked asset `a`,
  and any chain `c` for the token model's mints and burns).  Then a registry run from
  `W₁` with log `L` exists, and EVERY registry run from `W₁` with log `L` ends in a
  world `W'` where:
  - `W'` is the end of a bounded run from fresh storage, and of a tightened run if `W`
    was; its vault is the registration's write; `t` corresponds to it; both models'
    invariants hold;
  - the asset's recorded outflow is `lifecycleOutTotal trace` (all it prepared or
    burned) and its recorded inflow `lifecycleInTotal trace` (all it minted);
  - the token's supply plus that outflow equals that inflow, and the identity pins the
    supply: `n + outflow = inflow` holds for `n` = the token's supply and for no other
    `n` (contrast `UnifiedLifecycleSupplyConjunctFree`);
  - every other asset's recorded total outflow and inflow are those of `W`.

  `Contracts.NativeTokenVault.Properties.ReachLogDeterministic` makes the run with log
  `L` unique, so `W'` is a function of `W`, the registration, the trace and `c` (which
  only moves the per-chain records).  The proof module also rederives
  `UnifiedLifecycleCorresponds` from this statement
  (`unifiedLifecycleCorresponds_of_traced`).

The step-level matching behind it is `Properties.LifecycleRelIsSimulation`'s; the proof
module adds the label of the matched step (`lifecycleRel_stepOp`).  The identity holds
for the MATCHED run only: other registry runs from `W₁` can break it
(`Properties.LifecycleIdentityNotRegistryInvariant`).  Hash premise: the bounded
`IdAssumptionsOn e S` of `UnifiedLifecycleCorresponds`, on the registry prefix's pairs
and the registered pair; the matched steps are flows, which hash nothing.

## Anti-vacuity

`UnifiedLifecycleTracedSatisfiable`: every premise of `UnifiedLifecycleTraced`,
`UnifiedLifecycleSupplyConjunctFree` and `LifecycleLoggedSupply`, with a registry prefix
that registers an asset and a logged run whose prepared-or-burned and minted totals are
both one and whose matched registry log is one `bridgeIn` and then one `bridgeOut`, each
of one unit (the proof's witness: a mint of one unit, then a preparation of it).  `LifecycleRepReachIffReachLog` has no premise.
-/

namespace Contracts.NativeTokenVaultBase

open NativeTokenVault (Chain World NtvAssetId Valid IdAssumptionsOn)

/-! ## Logging loses no run -/

/-- **LOGGING LOSES NO RUN.**  `RepReach` and `LifecycleReachLog` relate the same
states: every run of the representation model's life has a log, and every logged run is
a run. -/
def Properties.LifecycleRepReachIffReachLog : Prop :=
  ∀ (Accounting : Type) (hooks : Hooks Accounting) (s t : State Accounting),
    RepReach hooks s t ↔ ∃ trace, LifecycleReachLog hooks s t trace

/-! ## The supply along a logged run -/

/-- **THE SUPPLY IS WHAT THE LOG MINTED, LESS WHAT IT PREPARED OR BURNED.**  Along a
logged run from a `WellFormed` state, `WellFormed` and the configuration are kept, and
the end supply plus everything the log prepared or burned equals the starting supply
plus everything it minted.  A statement about the representation model alone. -/
def Properties.LifecycleLoggedSupply : Prop :=
  ∀ (Accounting : Type) (hooks : Hooks Accounting) (s t : State Accounting)
    (trace : List LifecycleOp),
    WellFormed s → LifecycleReachLog hooks s t trace →
      WellFormed t ∧ t.config = s.config
      ∧ t.token.totalSupply + lifecycleOutTotal trace
          = s.token.totalSupply + lifecycleInTotal trace

/-! ## The lifecycle correspondence, tied to the trace -/

/-- **THE MATCHED REGISTRY RUN.**  Premises: those of `UnifiedLifecycleCorresponds`
(a bounded registry run from fresh storage to `W`, under the bounded hash premise on its
pair set `S`, with a nonzero chain id; a registration state corresponding to `W.vault`
whose (origin chain, origin token) pair is in `S`; a successful tightened registration,
the asset encoders agreeing at that pair), with the run from the registered state to `t`
logged as `trace`.

Let `W₁` be the world carrying the registration's write and `L` the registry log matched
with `trace` (`lifecycleRegistryLog`, for the tracked asset; the token model's mints and
burns attributed to any chain `c`).  Conclusion: a registry run from `W₁` with log `L`
exists; and for EVERY registry run from `W₁` with log `L`, its end `W'`

* is the end of a bounded run from fresh storage, and of a tightened run if `W` was;
* has the registration's write as its vault, corresponding to `t`, with `Valid`; and
  `t` is `WellFormed`;
* records exactly the trace's prepared-or-burned total as the asset's outflow and its
  minted total as the asset's inflow;
* satisfies the supply identity, which determines the supply: `n` plus the recorded
  outflow equals the recorded inflow iff `n` is the token's total supply;
* records, for every other asset, the total outflow and inflow `W` recorded.

The run with log `L` is unique (`ReachLogDeterministic`), so the identity is about the
registry run that the trace determines, not about a run chosen to fit
(`UnifiedLifecycleSupplyConjunctFree`).  It is not a registry invariant: other registry
runs from `W₁` can break it (`LifecycleIdentityNotRegistryInvariant`). -/
def Properties.UnifiedLifecycleTraced : Prop :=
  ∀ (Accounting : Type) (rhooks : RegistrationHooks Accounting) (hooks : Hooks Accounting)
    (s : RegistrationState Accounting) (origin : Address) (reg : Registered Accounting)
    (t : State Accounting) (trace : List LifecycleOp) (e : NtvAssetId)
    (S : Set (Chain × NativeTokenVault.Address)) (thisChain c : Chain) (W : World),
    IdAssumptionsOn e S → thisChain ≠ 0 →
    NativeTokenVault.ReachIn e thisChain S NativeTokenVault.empty W →
    (s.config.originChainId, widen origin) ∈ S →
    CorrPre s thisChain W.vault → registerFreshBranch' rhooks s origin = some reg →
    rhooks.assetIdFor s.config.originChainId origin = e s.config.originChainId (widen origin) →
    LifecycleReachLog hooks reg.state t trace →
      (∃ W' : World, NativeTokenVault.ReachLog e thisChain
          { W with vault := correspondingRegistration s origin W.vault } W'
          (lifecycleRegistryLog s.config.assetId c trace))
      ∧ ∀ W' : World, NativeTokenVault.ReachLog e thisChain
          { W with vault := correspondingRegistration s origin W.vault } W'
          (lifecycleRegistryLog s.config.assetId c trace) →
        NativeTokenVault.ReachIn e thisChain S NativeTokenVault.empty W'
        ∧ (NativeTokenVault.Reach' e thisChain NativeTokenVault.empty W →
            NativeTokenVault.Reach' e thisChain NativeTokenVault.empty W')
        ∧ W'.vault = correspondingRegistration s origin W.vault
        ∧ Corr t thisChain W'.vault ∧ Valid e thisChain W'.vault ∧ WellFormed t
        ∧ W'.audit.totalOut s.config.assetId = lifecycleOutTotal trace
        ∧ W'.audit.totalIn s.config.assetId = lifecycleInTotal trace
        ∧ t.token.totalSupply + lifecycleOutTotal trace = lifecycleInTotal trace
        ∧ (∀ n : ℕ, n + W'.audit.totalOut s.config.assetId = W'.audit.totalIn s.config.assetId
            ↔ n = t.token.totalSupply)
        ∧ ∀ b, b ≠ s.config.assetId →
            W'.audit.totalOut b = W.audit.totalOut b ∧ W'.audit.totalIn b = W.audit.totalIn b

/-! ## Why the existential form says nothing about the supply -/

/-- **`UnifiedLifecycleCorresponds`'s IDENTITY CONJUNCT IS FREE.**  Under the premises of
`UnifiedLifecycleCorresponds`, its whole conclusion holds with any number `n` in place of
the tracked token's total supply.  The registry world is existential there, and one more
flow step of the tracked asset (a `bridgeIn` or a nonzero `bridgeOut`, guarded only by
registration, leaving the vault of a non-native asset unchanged) sets its recorded inflow
minus outflow to `n`.  So that conjunct carries no information about the representation
model's run; `UnifiedLifecycleTraced` is the form where it does.  Negative result; its
premises are met by `UnifiedLifecycleSatisfiable` and `UnifiedLifecycleTracedSatisfiable`. -/
def Properties.UnifiedLifecycleSupplyConjunctFree : Prop :=
  ∀ (Accounting : Type) (rhooks : RegistrationHooks Accounting) (hooks : Hooks Accounting)
    (s : RegistrationState Accounting) (origin : Address) (reg : Registered Accounting)
    (t : State Accounting) (e : NtvAssetId) (S : Set (Chain × NativeTokenVault.Address))
    (thisChain : Chain) (W : World) (n : ℕ),
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
        ∧ n + W'.audit.totalOut s.config.assetId = W'.audit.totalIn s.config.assetId

/-! ## Anti-vacuity -/

/-- **THE PREMISES ARE SATISFIABLE, NONTRIVIALLY.**  Every premise of
`UnifiedLifecycleTraced`, of `UnifiedLifecycleSupplyConjunctFree` (the unlogged run) and
of `LifecycleLoggedSupply` (the registered state is `WellFormed`), on a registry prefix
that registers an asset, with a logged run whose prepared-or-burned and minted totals
are both one and whose matched registry log (chain `c` taken to be the origin chain) is
one `bridgeIn` and then one `bridgeOut` towards some chain, each of one unit of the
tracked asset.  The proof's run mints one unit and then prepares it. -/
def Properties.UnifiedLifecycleTracedSatisfiable : Prop :=
  ∃ (rhooks : RegistrationHooks Unit) (hooks : Hooks Unit) (s : RegistrationState Unit)
    (origin : Address) (reg : Registered Unit) (t : State Unit) (trace : List LifecycleOp)
    (e : NtvAssetId) (S : Set (Chain × NativeTokenVault.Address)) (thisChain : Chain)
    (W : World),
    IdAssumptionsOn e S ∧ thisChain ≠ 0
    ∧ NativeTokenVault.ReachIn e thisChain S NativeTokenVault.empty W
    ∧ (s.config.originChainId, widen origin) ∈ S
    ∧ CorrPre s thisChain W.vault ∧ registerFreshBranch' rhooks s origin = some reg
    ∧ rhooks.assetIdFor s.config.originChainId origin = e s.config.originChainId (widen origin)
    ∧ LifecycleReachLog hooks reg.state t trace ∧ RepReach hooks reg.state t
    ∧ WellFormed reg.state
    ∧ (∃ b, NativeTokenVault.Registered W.vault b)
    ∧ lifecycleOutTotal trace = 1 ∧ lifecycleInTotal trace = 1
    ∧ ∃ d : Chain, lifecycleRegistryLog s.config.assetId s.config.originChainId trace
        = [.bridgeIn s.config.originChainId s.config.assetId 1,
           .bridgeOut d s.config.assetId 1]

end Contracts.NativeTokenVaultBase
