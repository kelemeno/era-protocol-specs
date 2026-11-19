import EraSpec.Contracts.ProxyUpgradeExecutorBase.History.Specs.DomainHoldersD9

/-!
# History properties: the `d9f6789` leg compared with the `b17415d20` one

**The record of an older commit, not a claim about `b17415d20`.** Statements about
`EraSpec.Contracts.ProxyUpgradeExecutorBase.History.Specs.DomainHoldersD9`; proofs in
`EraSpec.Contracts.ProxyUpgradeExecutorBase.History.Proofs.DomainHoldersD9`. `leg` is the
`b17415d20` leg of `Contracts.DomainHoldersV35`; `D9.leg` is the `d9f6789` leg.

`AliasingPassesAtD9CaughtAtB17` is the comparison: an engine that first makes the CTM's `admin`
the `ProxyAdmin` and then moves the CTM proxy's admin slot passes `D9.leg` for every hash
function, and with the same engine `leg` reverts or its compared pair collides. The comment at
`ProxyUpgradeExecutorBase.sol:72-74` (at `b17415d20`), added with the check in `9775be946`,
describes this case. The `b17415d20` halves of `MovedCtmCaughtNotVacuous` and
`MovedCtmWithCtmRowReverts` are `Contracts.DomainHoldersV35.Properties.MovedCtmCaughtWitness` and
`Contracts.DomainHoldersV35.Properties.MovedCtmWithCtmRowLegReverts`.
-/

namespace Contracts.DomainHoldersV35.History

/-- **`MovedCtmCaught` IS NOT VACUOUS, ITS DISJUNCT IS NOT A TAUTOLOGY, AND THE INSTANCE PASSES
AT `d9f6789`.** A CTM executor in its standing configuration, with a nonzero notifier, the
check at `:75-77` passing, nonempty participating rows already applied, and the engine
`aliasCtmProxyAdmin X` for an `X` other than zero, the executor and the `ProxyAdmin`: every
premise of `MovedCtmCaught` holds, the engine moves the CTM proxy's admin slot to `X`, `leg`
reverts, the pair does not collide under the environment's hash, and `D9.leg` with the same
engine succeeds with the same post-state. -/
def Properties.MovedCtmCaughtNotVacuous : Prop :=
  ∃ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (w w' : World) (X : Address),
    Prechecks E B tr m ∧ ExecutorHoldsCtm B w ∧ CtmAdminOk B w ∧ w.serverNotifier ≠ 0
    ∧ toRows m.proxyUpgrades ≠ [] ∧ rowsApplied B w (toRows m.proxyUpgrades)
    ∧ X ≠ 0 ∧ X ≠ B.self ∧ X ≠ B.pa
    ∧ aliasCtmProxyAdmin X B.self (buildContext B tr m) m.proxyUpgrades w = some w'
    ∧ (w'.proxy B.ctm).adminSlot = X
    ∧ leg E B tr m (aliasCtmProxyAdmin X) w = none
    ∧ ¬ HolderPairCollides B E.H w w'
    ∧ D9.leg E B tr m (aliasCtmProxyAdmin X) w = some w'

/-- **THE ROWS POST-CHECK REVERTS A MOVED CTM THAT HAS A ROW.** If the engine's post-state has
the CTM proxy administered by anything but the `ProxyAdmin`, the CTM's implementation has no
`implementation()` (as `ChainTypeManager`), and the transition has a participating row on the
CTM proxy, then `requireRowsApplied` (`:103`) reverts: both `leg` and `D9.leg` revert, for
every hash function. -/
def Properties.MovedCtmWithCtmRowReverts : Prop :=
  ∀ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (eng : Engine) (w w' : World),
    eng B.self (buildContext B tr m) m.proxyUpgrades w = some w' →
    (w'.proxy B.ctm).adminSlot ≠ B.pa →
    w'.implAnswer B.ctm = none →
    (∃ r ∈ toRows m.proxyUpgrades, r.proxy = B.ctm) →
    leg E B tr m eng w = none ∧ D9.leg E B tr m eng w = none

/-- **THE ALIASING ENGINE PASSES AT `d9f6789` AND IS CAUGHT AT `b17415d`.** Take a CTM executor
in its standing configuration (`ExecutorHoldsCtm`), a transition passing the prechecks, and an
engine that first runs any prefix `pre` (for example the rows) leaving the `d9f6789` holder
reads alone (`D9.HolderFrame`) with every participating row applied and none on the CTM proxy,
and then runs `aliasCtmProxyAdmin X` for any `X` other than zero, the executor and the
`ProxyAdmin`. Then there is a post-state `w₂` such that:
* `D9.leg` succeeds with `w₂`, **for every hash function**;
* the CTM proxy's admin slot is `X`, its implementation is unchanged, and the CTM's `admin`
  is the `ProxyAdmin`;
* the `d9f6789` CTM tuple read after is the one read before, word for word, and so is the
  outer notifier tuple;
* `X` administers the CTM proxy: an `upgradeTo` it sends with code installs that code as the
  CTM's implementation;
* the executor's `ProxyAdmin` does not: its `changeProxyAdmin` to any address reverts, and so
  does an `upgradeTo` from it;
* `leg` (`b17415d`) with the same engine reverts, or its compared pair collides.
The last conjunct has no `CtmAdminOk` premise, so it also covers starts where the CTM's
`admin()` already is the `ProxyAdmin`; there `leg` reverts at the pre-check (`:75-77`), not at
the hash comparison. `MovedCtmCaughtNotVacuous` is the instance with `CtmAdminOk`, a hash that
separates the pair, and a revert at the comparison. -/
def Properties.AliasingPassesAtD9CaughtAtB17 : Prop :=
  ∀ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (pre : Engine) (w₀ w₁ : World)
    (X : Address),
    Prechecks E B tr m → ExecutorHoldsCtm B w₀ →
    pre B.self (buildContext B tr m) m.proxyUpgrades w₀ = some w₁ →
    D9.HolderFrame B w₀.serverNotifier w₀ w₁ →
    rowsApplied B w₁ (toRows m.proxyUpgrades) →
    (∀ r ∈ toRows m.proxyUpgrades, r.proxy ≠ B.ctm) →
    X ≠ 0 → X ≠ B.self → X ≠ B.pa →
    ∃ w₂, D9.leg E B tr m (pre.andThen (aliasCtmProxyAdmin X)) w₀ = some w₂
      ∧ (w₂.proxy B.ctm).adminSlot = X
      ∧ (w₂.proxy B.ctm).impl = (w₀.proxy B.ctm).impl
      ∧ w₂.adminAnswer B.ctm = some B.pa
      ∧ D9.ctmWords B w₂ = D9.ctmWords B w₀
      ∧ D9.notifierWords B E.H w₂ w₀.serverNotifier
          = D9.notifierWords B E.H w₀ w₀.serverNotifier
      ∧ (∀ impl, E.hasCode impl = true →
          tupAdminUpgradeTo E.hasCode (w₂.proxy B.ctm) X impl
            = some { (w₂.proxy B.ctm) with impl := impl })
      ∧ (∀ a, paChangeProxyAdmin w₂ B.pa B.self B.ctm a = none)
      ∧ (∀ impl, tupAdminUpgradeTo E.hasCode (w₂.proxy B.ctm) B.pa impl = none)
      ∧ (leg E B tr m (pre.andThen (aliasCtmProxyAdmin X)) w₀ = none
          ∨ HolderPairCollides B E.H w₀ w₂)

/-- **THE PREMISES OF `AliasingPassesAtD9CaughtAtB17` HOLD TOGETHER**, with a nonzero
notifier, a nonempty set of participating rows (a transition must have one,
`upgrades/registry/objects/ProxyUpgradeTransition.sol:34-36`) that the prefix applies and that
are not applied before it, the check at `:75-77` passing, and an `X` meeting the side
conditions. -/
def Properties.AliasingPassesAtD9CaughtAtB17Satisfiable : Prop :=
  ∃ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (pre : Engine) (w₀ w₁ : World)
    (X : Address),
    Prechecks E B tr m ∧ ExecutorHoldsCtm B w₀ ∧ CtmAdminOk B w₀ ∧ w₀.serverNotifier ≠ 0
    ∧ pre B.self (buildContext B tr m) m.proxyUpgrades w₀ = some w₁
    ∧ D9.HolderFrame B w₀.serverNotifier w₀ w₁
    ∧ toRows m.proxyUpgrades ≠ [] ∧ ¬ rowsApplied B w₀ (toRows m.proxyUpgrades)
    ∧ rowsApplied B w₁ (toRows m.proxyUpgrades)
    ∧ (∀ r ∈ toRows m.proxyUpgrades, r.proxy ≠ B.ctm)
    ∧ X ≠ 0 ∧ X ≠ B.self ∧ X ≠ B.pa

end Contracts.DomainHoldersV35.History
