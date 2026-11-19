import EraSpec.Contracts.ProxyUpgradeExecutorBase.Specs.CoreLegRefinement

/-!
# Properties: the Core leg is the canonical leg in the Core domain

Statements about `EraSpec.Contracts.ProxyUpgradeExecutorBase.Specs.CoreLegRefinement`. Proofs
are in `EraSpec.Contracts.ProxyUpgradeExecutorBase.Proofs.CoreLegRefinement`.

* `CoreLegIsDomainHoldersLeg`: for every engine of `DomainHoldersV35` that does, on the
  embedded starting world, what the `CoreLeg` engine does (up to the embedding), the embedded
  result of the `CoreLeg` leg in the Core domain is the `DomainHoldersV35` leg's result. Equal
  as options: the two legs revert together, and succeed with the same world.
  `CoreLegIsDomainHoldersLegSatisfiable` is the witness that its premise can be met.
* `CoreLegKeepsPAOwnerViaDomainHolders`: the `ProxyAdmin`-owner part of `CoreLegChecks`,
  derived through it from `DomainHoldersV35`'s `PassingLegKeepsHolderReads`.
-/

namespace Contracts.CoreLegRefinement

open Contracts.ProxyUpgradeExecutorV35

/-- **THE CORE LEG IS THE CANONICAL LEG IN THE CORE DOMAIN.** For every Core executor `X`,
engines `E`, transition `T`, world `W`, filler world `w₀` and `DomainHoldersV35` engine `eng`: if
`eng`, run on the embedded `W` with the context `DomainHoldersV35` builds, returns the embedding
of what `T`'s engine returns on `W`, then the embedding of the Core leg's result on `W` is the
`DomainHoldersV35` leg's result on the embedded `W`. -/
def Properties.CoreLegIsDomainHoldersLeg : Prop :=
  ∀ (X : CoreLeg.Exec) (E : CoreLeg.Engines) (T : CoreLeg.TransitionObj) (W : CoreLeg.World)
    (w₀ : DomainHoldersV35.World) (eng : DomainHoldersV35.Engine),
    eng X.self (DomainHoldersV35.buildContext (bindings X) T.addr (manifestMap T.manifest))
        (manifestMap T.manifest).proxyUpgrades (embed X w₀ W)
      = (E T.manifest.engine (CoreLeg.context X T .core 0) T.manifest.proxyUpgrades W).map
          (embed X w₀) →
    (CoreLeg.applyProxyUpgradeTransition X E T .core 0 W).map (embed X w₀)
      = DomainHoldersV35.leg (env X) (bindings X) T.addr (manifestMap T.manifest) eng
          (embed X w₀ W)

/-- **THE ENGINE-AGREEMENT PREMISE OF `CoreLegIsDomainHoldersLeg` IS SATISFIABLE.** For every
Core executor, engines, transition, world and filler world there is a `DomainHoldersV35` engine
meeting it: the one that returns the embedding of what `T`'s engine returns on `W`. -/
def Properties.CoreLegIsDomainHoldersLegSatisfiable : Prop :=
  ∀ (X : CoreLeg.Exec) (E : CoreLeg.Engines) (T : CoreLeg.TransitionObj) (W : CoreLeg.World)
    (w₀ : DomainHoldersV35.World), ∃ eng : DomainHoldersV35.Engine,
    eng X.self (DomainHoldersV35.buildContext (bindings X) T.addr (manifestMap T.manifest))
        (manifestMap T.manifest).proxyUpgrades (embed X w₀ W)
      = (E T.manifest.engine (CoreLeg.context X T .core 0) T.manifest.proxyUpgrades W).map
          (embed X w₀)

/-- **A CORE LEG KEEPS THE `ProxyAdmin`'S OWNER, OR ITS HASH COLLIDES**, derived from
`DomainHoldersV35.PassingLegKeepsHolderReads` through `CoreLegIsDomainHoldersLeg`. -/
def Properties.CoreLegKeepsPAOwnerViaDomainHolders : Prop :=
  ∀ (X : CoreLeg.Exec) (E : CoreLeg.Engines) (T : CoreLeg.TransitionObj) (W W' : CoreLeg.World),
    CoreLeg.applyProxyUpgradeTransition X E T .core 0 W = some W' →
    W'.paOwner = W.paOwner ∨
      (W'.paOwner ≠ W.paOwner ∧ X.keccakOwner W'.paOwner = X.keccakOwner W.paOwner)

end Contracts.CoreLegRefinement
