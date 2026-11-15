import EraSpec.Contracts.ChainTypeManager.Specs.ExecutorUpgradeChain
import EraSpec.Contracts.ChainTypeManager.Specs.ChainLocalExecutor
import EraSpec.Contracts.ChainTypeManager.Specs.Enabledness

/-!
# Model: a pre-v35 chain crossing an opaque legacy edge from its own diamond

Source: the CTM at branch `feat/upgrade-simplification`, commit `e561b9cc2`, as for the rest of
this folder, and the pre-v35 chain-side `Admin` facet at the pinned era-contracts commit
`c67894b9`. Paths are relative to `l1-contracts/contracts/`, except those starting with `docs/`,
which are at the root of the `e561b9cc2` repository.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainTypeManager.Properties.LegacyCrossingFaithful` and are proved in
`EraSpec.Contracts.ChainTypeManager.Proofs.LegacyCrossingFaithful`. Everything here is in the
sub-namespace `Contracts.ChainTypeManager.LegacyCrossing`. It adds one step and edits no existing
definition.

## The missing step

`ChainRouting` models two source behaviours with one label, `Label.arbitraryCut`
(`Specs/ChainRouting.lean`, "Break-glass"): the CTM owner's `executeUpgrade`, and crossing an
opaque legacy edge. Only the first of these is owner-only. A chain whose diamond still runs a
v31-v34 `Admin` facet exposes the cut-taking upgrade entry point
(`state-transition/chain-interfaces/IAdminWithCut.sol:7-22` at `e561b9cc2`). Its code, at
`c67894b9` (`state-transition/chain-deps/facets/Admin.sol:494-525`), is:

    function upgradeChainFromVersion(address, uint256 _oldProtocolVersion,
        Diamond.DiamondCutData calldata _diamondCut) external onlyAdminOrChainTypeManagerOrValidator {
        bytes32 cutHashInput = keccak256(abi.encode(_diamondCut));
        bytes32 upgradeCutHash = IChainTypeManager(s.chainTypeManager).upgradeCutHash(_oldProtocolVersion);
        if (cutHashInput != upgradeCutHash) { revert HashMismatch(upgradeCutHash, cutHashInput); }
        if (s.protocolVersion != _oldProtocolVersion) { revert ProtocolIdMismatch(...); }
        ... ServerNotifier gate, for callers other than the admin and the CTM ...
        _executeDiamondCut(_diamondCut);
        if (s.protocolVersion <= _oldProtocolVersion) { revert ProtocolIdNotGreater(); }

The modifier lets the chain's admin, its CTM and its validators call (`ZKChainBase.sol:140-145` at
`c67894b9`). The CTM at `e561b9cc2` still serves the commitment: `upgradeCutHash` returns
`__LEGACY_upgradeCutHash` (`state-transition/ChainTypeManager.sol:871-878`: "their Admin facets
verify the handed cut against this"). The authority matrix lists this entry point with the chain
admin on the chain side (`docs/registry-driven-upgrades.md:402`), and the bootstrap section says
pre-v35 chains cross "through the legacy cut-taking chain entrypoint: from their admin, or from
governance ... (`forward`)" (:895-897).

So a pre-v35 chain's admin or validator can cross any legacy-committed edge at the chain's version
directly on the diamond, without the CTM owner. In `ExecutorForward`, `arbitraryCut` occurs only as
a forwarded CTM call (`FCall.sys`), because `Label.isEnv` holds only for `genesis`, `migrateIn`
and `bootstrapReset` (`Specs/ExecutorForward.lean`, `Label.isEnv`). `FCall.Tame` excludes a forwarded
`arbitraryCut`. So no tame executor run contains a chain-side crossing of an opaque edge.
`ExecutorUpgradeChain`'s `adminUpgrade` is the post-v35 two-argument call (registry transitions
only), and `ChainLocalExecutor` reuses `Label.isEnv`. The chain-side crossing is missing from all
three. This file adds it as `CrossStep` and the label `LLabel.cross`.

Opaque legacy edges exist in reachable states:

* `bootstrapState W old R` records an opaque cut at every version below `old` (the pre-registry
  history).
* The CTM owner's `setUpgradeDiamondCut(cut, v)` (`ChainTypeManager.sol:842-855`, `Op.legacyRecut`)
  re-commits an arbitrary cut for a legacy-committed version, the bootstrap edge included. It is
  the "operational fix-up while pre-v35 chains still have to cross such an edge" (:835-837). A
  forward of it is `Tame` (`FCall.Tame` excludes only `arbitraryCut` and `swapCtm`).
* `setNewVersionUpgrade(cut, v, _, R)` with a cut other than the bootstrap's
  (`Op.legacyCommit R false`) records an opaque cut at the current version.

## The step

`CrossStep s id v ρ s'`: chain `id` is registered at version `c.pv`; the legacy cut committed for
`c.pv` is opaque; the chain lands at version `v` with routing `ρ`; `c.pv < v`
(`ProtocolIdNotGreater`, `Admin.sol:522-524`); the CTM and every other chain are untouched. What an
opaque cut installs is unknown to the model, so `v` and `ρ` are free beyond `c.pv < v`, exactly as
for `Label.arbitraryCut`.

## Modelling choices

* **Hash premises, pinned.** The crossing exists only at an opaque edge. Crossing a version
  with no legacy cut needs a `DiamondCutData` whose `keccak256(abi.encode(...))` is `bytes32(0)`
  (`upgradeCutHash` of an uncommitted version). Crossing the bootstrap edge with a cut other than
  the bootstrap's needs a second preimage of that one committed hash. Both are excluded, and only
  for those two hash values: no other hash property is assumed. The bootstrap edge itself is
  `Step.bootstrapReset`, which `ExecutorForward` already lets other actors take.
* **Callers are not modelled.** The admin, the CTM and the validators may all call. The
  validators' `ServerNotifier` gate only rejects. The CTM's own three-argument
  `upgradeChainFromVersion(chainId, old, cut)` (`ChainTypeManager.sol:826-833`, `onlyOwner`) reaches
  the same diamond function. Through the executor it is a forward of `arbitraryCut`, which is
  already in `ExecutorForward`.
* **Dispatch is not modelled**, as everywhere in this folder. The step exists for every chain at
  an opaque edge. In the source only a chain whose live routing still sends the selector to a
  v31-v34 `Admin` facet can take it: chains created by the registry CTM run v35+ facets and route
  only the two-argument form. Allowing more chains only adds runs. The witnesses use pre-registry
  chains of the bootstrap states.
* **Everything else is `ExecutorUpgradeChain`'s model, unchanged**: `LLabel.u` is a `UStep`, which
  covers every `ExecutorForward` transaction except `XLabel.upgradeChain`, which it refines.
  Every `ExecutorForward` run is a `URun` (`Properties.ExecutorRunsNeedNoUpgradeChain`).

## Two readings of "tame"

* `LLabel.ExecTame`: every **executor transaction** is `Tame`. A chain-side crossing is not an
  executor transaction. This is how the `Tame` premise of `TameRunPreservesSysInv` and its
  successors reads against the source, where the owner never issues the crossing.
* `LLabel.Tame`: the fix proposed for the gap. A chain-side crossing counts as break-glass, so a
  run with any crossing is not tame. Under this reading the old results stand unchanged
  (`Properties.TameRefinedRunKeepsChainsOnTheirRelease`), but they say nothing about a system in
  which a pre-v35 chain's admin is active.
-/

namespace Contracts.ChainTypeManager.LegacyCrossing

/-! ## The chain-side crossing -/

/-- The system after chain `id` lands at version `v` with routing `ρ`: the write of a
break-glass cut, and of a crossing of an opaque legacy edge. -/
def landAt (s : Sys) (id : ChainId) (v : ℕ) (ρ : Routing) : Sys :=
  { s with chains := upd s.chains id (some ⟨v, ρ⟩) }

/-- **Chain `id` crosses the opaque legacy edge at its version from its own diamond**: the
pre-v35 `Admin.upgradeChainFromVersion(_, c.pv, cut)` (`c67894b9`
`state-transition/chain-deps/facets/Admin.sol:494-525`), called by the chain's admin or a
validator, with the cut the CTM committed for `c.pv`. That cut is opaque. The chain lands at a
version `v > c.pv` (`ProtocolIdNotGreater`, :522-524) with routing `ρ`. Code that the cut's init
runs acts as that diamond, which is neither the CTM's owner nor another diamond's
`chainTypeManager`. So, as for `Step.arbitraryCut`, the CTM and the other chains are untouched
(`Specs/ChainLocal.lean`, *Why a per-chain statement*). -/
inductive CrossStep (s : Sys) (id : ChainId) (v : ℕ) (ρ : Routing) : Sys → Prop
  | mk {c : Chain} :
      s.chains id = some c →
      s.ctm.legacy c.pv = LegacyCut.opaque →
      c.pv < v →
      CrossStep s id v ρ (landAt s id v ρ)

/-- What happens: `ExecutorUpgradeChain`'s transactions, and a pre-v35 chain's own crossing of an
opaque legacy edge. -/
inductive LLabel
  /-- An `ExecutorUpgradeChain` transaction: an `ExecutorForward` transaction other than
  `XLabel.upgradeChain`, the executor's `upgradeChain(t, id)`, or the chain admin's two-argument
  `Admin.upgradeChainFromVersion`. -/
  | u (l : ULabel)
  /-- Chain `id`'s admin or validator crossing the opaque legacy edge at the chain's version,
  landing at version `v` with routing `ρ`. -/
  | cross (id : ChainId) (v : ℕ) (ρ : Routing)

/-- One successful transaction. -/
inductive LStep (X : XConfig) : XState → LLabel → XState → Prop
  /-- Exactly as in `ExecutorUpgradeChain`. -/
  | u {s s' : XState} {l : ULabel} : UStep X s l s' → LStep X s (.u l) s'
  /-- The chain-side crossing: the CTM, every other chain and every proxy are untouched. -/
  | cross {s : XState} {id : ChainId} {v : ℕ} {ρ : Routing} {sys' : Sys} :
      CrossStep s.sys id v ρ sys' → LStep X s (.cross id v ρ) { s with sys := sys' }

/-- A sequence of successful transactions. -/
inductive LRun (X : XConfig) : XState → List LLabel → XState → Prop
  | nil {s : XState} : LRun X s [] s
  | cons {s s' s'' : XState} {l : LLabel} {ls : List LLabel} :
      LStep X s l s' → LRun X s' ls s'' → LRun X s (l :: ls) s''

/-! ## Premises -/

/-- Every executor transaction is `Tame` (`ULabel.Tame`). A chain-side crossing is no executor
transaction, so it is not constrained. -/
def LLabel.ExecTame (X : XConfig) : LLabel → Prop
  | .u l => l.Tame X
  | .cross _ _ _ => True

/-- The fix proposed for the gap: a chain-side crossing is not tame. -/
def LLabel.Tame (X : XConfig) : LLabel → Prop
  | .u l => l.Tame X
  | .cross _ _ _ => False

/-- Every executor transaction leaves the CTM proxy's implementation in place
(`XLabel.KeepsCtmCode`). A chain-side crossing touches no proxy. -/
def LLabel.KeepsCtmCode (X : XConfig) : LLabel → Prop
  | .u l => l.toX.KeepsCtmCode X
  | .cross _ _ _ => True

/-- `replaceUpgradeTransition(e, r)` is one of the calls a transaction forwards. -/
def LLabel.ForwardsReplace (e r : Address) : LLabel → Prop
  | .u l => l.ForwardsReplace e r
  | .cross _ _ _ => False

/-- The routing steps a transaction takes, in order. An executor transaction takes those of its
`ExecutorForward` label (`XLabel.sysLabels`); a chain-side crossing is, from the chain's point of
view, the break-glass write `Label.arbitraryCut` with the same chain, version and routing. -/
def LLabel.sysLabels : LLabel → List Label
  | .u l => l.toX.sysLabels
  | .cross id v ρ => [.arbitraryCut id v ρ]

/-- A crossing to version `v` with routing `ρ` lands the chain consistent with the CTM in state
`s`: not ahead of it, and on exactly `R_v`'s routing if the CTM has a release for `v`. This is
`ChainOk` of the landed chain. It is a property of the opaque cut, which the CTM owner chose when
committing it. -/
def CrossLandsOk (W : World) (s : Sys) (v : ℕ) (ρ : Routing) : Prop :=
  v ≤ s.ctm.pv ∧ (s.ctm.relAt v ≠ 0 → ρ = rowsRouting (W.relRows (s.ctm.relAt v)))

/-- The landing premise of one transaction in state `s`: a crossing lands consistently; an
executor transaction is unconstrained here. -/
def LLabel.LandsOk (W : World) (s : Sys) : LLabel → Prop
  | .u _ => True
  | .cross _ v ρ => CrossLandsOk W s v ρ

/-- A refined run in which every chain-side crossing, in the state where it is taken, lands its
chain consistent with the CTM. -/
inductive LRunOk (X : XConfig) : XState → List LLabel → XState → Prop
  | nil {s : XState} : LRunOk X s [] s
  | cons {s s' s'' : XState} {l : LLabel} {ls : List LLabel} :
      LStep X s l s' → l.LandsOk X.W s.sys → LRunOk X s' ls s'' → LRunOk X s (l :: ls) s''

/-! ## Witness data

On `ExecutorForward`'s witness executor `wX` (the witness world `wWorld`, the row library's
witness configuration, the CTM proxy `8`), with every proxy at implementation `10`. -/

/-- The just-bootstrapped system of `ChainRouting`'s bootstrap witness, as an executor state.
The CTM is `bootstrapState wWorld 0 100`: version 1 on release `100`, the bootstrap cut recorded at
version 0. Pre-registry chain `5` is at version 0 and routes only selector `7`. -/
def wLX0 : XState := ⟨wBootSys, ProxyUpgradeCurrent.wImpl⟩

/-- The countermodel run from `wLX0`. One `forward` of `setUpgradeDiamondCut(cut, 0)` re-commits
the bootstrap edge with a cut the model cannot see (`Op.legacyRecut 0`). Chain `5`'s admin then
crosses that edge on its own diamond, landing at version 1 with routing `bgExtra` (release
`100`'s routing plus selector `9`). -/
def wRecutRun : List LLabel :=
  [.u (.x (.forward [.sys (.ctm (.legacyRecut 0))])), .cross 5 1 bgExtra]

/-- `Enabledness`'s just-bootstrapped system with two pre-registry chains behind the CTM, as an
executor state. The CTM is `bootstrapState wWorld 1 200`: version 2 on release `200`, the bootstrap
cut recorded at version 1, an opaque pre-registry cut at version 0. Chain `5` is at version 0 and
chain `6` at version 1. -/
def wLagX0 : XState := ⟨wLagSys, ProxyUpgradeCurrent.wImpl⟩

/-- The routing the pre-registry cut at version 0 leaves chain `5` with: its selector `7` moved
to facet `78`. -/
def wPreRoute : Routing := upd emptyRouting 7 (some (78, true))

/-- The catch-up run from `wLagX0`, with no executor transaction. Chain `5`'s admin crosses the
opaque pre-registry edge at version 0 to version 1, a version with no registry release. The
chain then crosses the bootstrap edge onto release `200` at version 2. -/
def wCatchUpRun : List LLabel :=
  [.cross 5 1 wPreRoute, .u (.x (.env (.bootstrapReset 5)))]

end Contracts.ChainTypeManager.LegacyCrossing
