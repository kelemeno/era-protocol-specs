import EraSpec.Contracts.ProxyUpgradeExecutorBase.Specs.CoreLegV35
import EraSpec.Contracts.ProxyUpgradeExecutorBase.Specs.DomainHoldersV35

/-!
# Model bridge: the Core leg is the canonical leg in the Core domain

Source: era-contracts `draft/v0.35.0` at commit `b17415d20`,
`upgrades/registry/executors/ProxyUpgradeExecutorBase.sol:51-104` (the leg) and
`executors/CoreUpgradeExecutor.sol:33-36` (its Core-domain entry point), as for both models
related here. `DomainHoldersV35` (`Contracts.DomainHoldersV35.leg`) is this folder's canonical
model of the leg, for both domains. `CoreLegV35` (`Contracts.ProxyUpgradeExecutorV35.CoreLeg`)
models the Core-domain leg in a world of its own, with implementation answers that may depend
on the world and reinitializers that write both slots. This file embeds a `CoreLeg` world into a
`DomainHoldersV35` world, so that the two legs can be compared
(`Properties/CoreLegRefinement.lean`).

**This file is definitions only.** The statements are in
`EraSpec.Contracts.ProxyUpgradeExecutorBase.Properties.CoreLegRefinement` and are proved in
`EraSpec.Contracts.ProxyUpgradeExecutorBase.Proofs.CoreLegRefinement`.

## The embedding

* The executor's owner and pending owner and the `ProxyAdmin`'s owner are copied.
* A proxy's two EIP-1967 slots are copied into its `Tup`.
* What a proxy's implementation answers to `implementation()` is fixed per proxy in
  `DomainHoldersV35`, and a function of the implementation, the proxy and the world in
  `CoreLeg`; the embedding of a world `W` evaluates it at `W`.
* The fields `DomainHoldersV35` keeps for the CTM domain (CTM and notifier reads) are taken
  from a fixed world `w₀`; the Core-domain leg reads none of them.
* `keccak256(abi.encode(owner))` (`CoreLeg`'s `keccakOwner`) is the hash of the one-word list
  `[owner]`; the inventory length is `inventoryLength`; rows keep their `proxy` and `implNew`.
-/

namespace Contracts.CoreLegRefinement

open Contracts.ProxyUpgradeExecutorV35

/-- `ProxyUpgradeDomain`, from the row library's encoding to `DomainHoldersV35`'s. -/
def domainMap : Contracts.ProxyUpgradeCurrent.Domain → DomainHoldersV35.Domain
  | .core => .core
  | .ctm => .ctm

/-- The two fields of a row that `DomainHoldersV35` keeps. -/
def rowMap (r : Contracts.ProxyUpgradeCurrent.Row) : DomainHoldersV35.Row := ⟨r.proxy, r.implNew⟩

/-- A `CoreLeg` transition's manifest as a `DomainHoldersV35` manifest. -/
def manifestMap (m : CoreLeg.Manifest) : DomainHoldersV35.Manifest :=
  ⟨domainMap m.domain, m.proxyUpgrades.map rowMap, m.engine⟩

/-- The Core executor's bindings: its address, its `ProxyAdmin`, the Core domain, no CTM. -/
def bindings (X : CoreLeg.Exec) : DomainHoldersV35.Bindings := ⟨X.self, X.pa, .core, 0⟩

/-- The environment: `keccak256(abi.encode(owner))` on the one-word list, `requireCode`, and
the inventory length. -/
def env (X : CoreLeg.Exec) : DomainHoldersV35.Env where
  H := fun l => X.keccakOwner (l.headD 0)
  hasCode := X.hasCode
  invLen := fun d => match d with
    | .core => CoreLeg.inventoryLength .core
    | .ctm => CoreLeg.inventoryLength .ctm

/-- A `CoreLeg` world as a `DomainHoldersV35` world, the CTM-domain fields taken from `w₀`. -/
def embed (X : CoreLeg.Exec) (w₀ : DomainHoldersV35.World) (W : CoreLeg.World) :
    DomainHoldersV35.World :=
  { w₀ with
    execOwner := W.owner
    execPendingOwner := W.pendingOwner
    paOwner := W.paOwner
    proxy := fun p => ⟨W.admin p, W.impl p⟩
    implAnswer := fun p => X.implAnswer (W.impl p) p W }

end Contracts.CoreLegRefinement
