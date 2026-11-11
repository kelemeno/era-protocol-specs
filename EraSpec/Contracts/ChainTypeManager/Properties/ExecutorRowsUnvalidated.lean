import EraSpec.Contracts.ChainTypeManager.Specs.ExecutorForward
import EraSpec.Contracts.ProxyUpgradeRowLib.Specs.RowsUnvalidated

/-!
# Properties: the executor's fixed entry points, for any transition object

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.ExecutorForward`, with the
row-library facts of `EraSpec.Contracts.ProxyUpgradeRowLib.Properties.RowsUnvalidated`.
Proofs are in `EraSpec.Contracts.ChainTypeManager.Proofs.ExecutorRowsUnvalidated`.

`applyInfrastructureUpgrade` takes any `IProxyUpgradeTransition`
(`upgrades/registry/executors/CTMUpgradeExecutor.sol:64-67`), and
`ProxyUpgradeRowLib.applyTransition` checks only its code and `domain()` before applying its
`rows()` (`upgrades/registry/libraries/ProxyUpgradeRowLib.sol:102-113`). The rows of an
object that is not a genuine `ProxyUpgradeTransition` were never validated and may name a
proxy twice. `FixedEntrypointsMoveProxiesOnlyAlongRows` (`Properties/ExecutorForward.lean`)
assumes that every applied transition's rows name distinct proxies.
`FixedEntrypointsMoveProxiesOnlyAlongRowsAnyRows` drops that premise. `ExecutorAnyRowsWitness`
applies a non-genuine transition with two rows on one proxy through the executor.
`forward` stays excluded: `ForwardDowngradesAProxy` still refutes the conclusion for it.
-/

namespace Contracts.ChainTypeManager

/-- **THE FIXED ENTRY POINTS MOVE A PROXY ONLY ALONG A ROW'S EDGE, FOR ANY TRANSITION
OBJECT.** Any executor step other than `forward`, with reinitializers that move at most their
own proxy, leaves every proxy where it was or moves it from some row's `expectedOldImpl` to
that row's `implNew`, where the row belongs to the transition the step applied. The transition
may be any object `applyInfrastructureUpgrade` accepts, genuine or not. This is
`FixedEntrypointsMoveProxiesOnlyAlongRows` without its distinct-proxies premise. -/
def Properties.FixedEntrypointsMoveProxiesOnlyAlongRowsAnyRows : Prop :=
  ∀ (X : XConfig) (s s' : XState) (x : XLabel), ProxyUpgradeCurrent.ReinitFrames X.rc →
    XStep X s x s' → (∀ calls, x ≠ .forward calls) → MovesOnlyAlongRows s s' x

/-- **THE PREMISES ARE MET BY A NON-GENUINE TRANSITION.** In the witness configuration
(reinitializers inert, so `ReinitFrames` holds), `applyInfrastructureUpgrade` on
`wDupTransition`, a CTM-domain object whose rows `6: 10 → 12` and `6: 11 → 12` name proxy `6`
twice, succeeds from the fresh witness state. The object is not genuine, so the premise
`FixedEntrypointsMoveProxiesOnlyAlongRows` takes fails for this step. The step is not a
`forward`, and it is `Tame`: its rows do not name the CTM proxy `8`. It leaves the CTM and its
chains alone and really moves proxy `6`, from `10` to `12`. -/
def Properties.ExecutorAnyRowsWitness : Prop :=
  ProxyUpgradeCurrent.ReinitFrames wX.rc ∧ ¬ ProxyUpgradeCurrent.wDupTransition.Genuine ∧
    ¬ ProxyUpgradeCurrent.wDupTransition.rows.Pairwise (fun a b => a.proxy ≠ b.proxy) ∧
    (∀ calls, XLabel.infra ProxyUpgradeCurrent.wDupTransition ≠ .forward calls) ∧
    XLabel.Tame wX (.infra ProxyUpgradeCurrent.wDupTransition) ∧
    ∃ s', XStep wX wX0 (.infra ProxyUpgradeCurrent.wDupTransition) s' ∧
      s'.sys = wX0.sys ∧ s'.impl 6 = 12 ∧ s'.impl 6 ≠ wX0.impl 6

end Contracts.ChainTypeManager
