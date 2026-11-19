import EraSpec.Contracts.ChainTypeManager.Specs.ExecutorForward

/-!
# Model: the executor's `upgradeChain`, with the lookup through its transition argument

Source: era-contracts branch `draft/v0.35.0` at commit `b17415d20`. Paths are relative to
`l1-contracts/contracts/` unless they start with `docs/` or `protocol-docs/`, which are at the
repository root; every `file:line` below is at `b17415d20`. The topic was first written at
`e561b9cc2` (branch `feat/upgrade-simplification`) and re-read at `b17415d20`: the executor's
`upgradeChain`, the CTM's `upgradeChainFromVersion` and `replaceUpgradeTransition`, the chain's
`Admin.upgradeChainFromVersion` and the engine's getters it cites are unchanged apart from line
numbers. The one change on these paths is that `Admin._executeDiamondCut` now ends with the
second-proof-system gate (`Admin.sol:121-126`, modelled in `ProofGateAtV35`); it only rejects,
and all three paths below face it alike.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainTypeManager.Properties.ExecutorUpgradeChain` and are proved in
`EraSpec.Contracts.ChainTypeManager.Proofs.ExecutorUpgradeChain`.

## Why this is refined

`ExecutorForward` models `CTMUpgradeExecutor.upgradeChain(_transition, _chainId)` by the bare
transition step: `XStep.upgradeChain` is `Step.transition`, and its label does not even carry
the transition argument. The entry point does more before the chain is reached
(`upgrades/registry/executors/CTMUpgradeExecutor.sol:92-107`):

    if (msg.sender != owner() && msg.sender != CHAIN_TYPE_MANAGER.getChainAdmin(_chainId)) {
        revert Unauthorized(msg.sender); }                                                // :93-95
    uint256 oldProtocolVersion = _transition.oldProtocolVersion();                        // :96
    address committed = CHAIN_TYPE_MANAGER.upgradeTransition(oldProtocolVersion);        // :99
    if (committed != address(_transition)) {
        revert TransitionNotCommitted(address(_transition), committed); }                 // :100-102
    CHAIN_TYPE_MANAGER.upgradeChainFromVersion(_chainId, oldProtocolVersion);            // :105
    emit ChainUpgradeApplied(_chainId, _transition.newProtocolVersion());                 // :106

So the slot it looks up, and the version it passes on, are what the **argument reports**
through `oldProtocolVersion()`. The CTM passes that version through unchanged
(`state-transition/ChainTypeManager.sol:618-621`):

    function upgradeChainFromVersion(uint256 _chainId, uint256 _oldProtocolVersion) external onlyOwner {
        address chainAddress = getZKChain(_chainId);
        IZKChain(chainAddress).upgradeChainFromVersion(chainAddress, _oldProtocolVersion);

and the chain's `Admin.upgradeChainFromVersion(_, _oldProtocolVersion)`
(`state-transition/chain-deps/facets/Admin.sol:559-590`) reads the cut its CTM derives from
`upgradeTransition[_oldProtocolVersion]` (:566-568, `ChainTypeManager.sol:601-607`) and
requires `s.protocolVersion == _oldProtocolVersion` (:570-572). From there on it is
`Step.transition`, which runs the slot at the chain's own version. Nothing on the chain's side
reads `oldProtocolVersion()`: the engine reads `fromRelease()`, `facetCuts()`,
`upgradeTarget()` and `l2Plan()` (`upgrades/DefaultUpgrade.sol:29-43, 65-84`), and the cut names
the transition only by address (`upgrades/registry/libraries/CTMUpgradeComposer.sol:37-43`).

A slot can hold an object whose report is not the slot: `replaceUpgradeTransition` writes the
slot the *replaced* transition reports and never compares the replacement's
`oldProtocolVersion()` with it (`ChainTypeManager.sol:428, 442`;
`Properties.NonGenuineReplacementBreaksSlotVersion`). A genuine `CTMTransition` reports its
departing release's version (`upgrades/registry/objects/CTMTransition.sol:61-64, 193-195`), and
`_requireSameDeparture` pins the departing release (`ChainTypeManager.sol:472-478`), so for genuine objects the two
agree. The coordination spec relies on that: a replacement "departs from the SAME release object
(and so the same version)" (`protocol-docs/ecosystem-upgrade-coordination.md:187`).

The same lookup is in `replaceUpgradeTransition` itself: it finds the slot to rewrite through
`_expectedTransition.oldProtocolVersion()` and requires the expected transition to be committed
there (`ChainTypeManager.sol:428-432`). That is `CStep.replace`'s premise
`s.ut (W.tr e).old = e`, already in `VersionRegistry`.

## Three ways for a chain to cross its edge

All three end in the chain's `Admin.upgradeChainFromVersion` and run the same engine; they differ
only in what comes before it.

* **`upgradeChain(t, id)`**, the executor's fixed entry point, for the executor's owner or the
  chain's own admin (`ULabel.upgradeChain`). The authority matrix lists it as the executors' path
  for `upgradeChainFromVersion` (`docs/registry-driven-upgrades.md:483`), and the NatSpec says to
  pass "the transition the CTM currently commits for the chain's departure ... after a
  replacement, the replacement" (`ICTMUpgradeExecutor.sol:55-56`).
* **The chain admin's direct call** of `Admin.upgradeChainFromVersion(_, old)` on its own diamond
  (`ULabel.adminUpgrade`): "Chain admins additionally retain their own direct path on the chain
  diamond" (`docs/registry-driven-upgrades.md:766`). The modifier admits the admin
  (`state-transition/chain-deps/facets/ZKChainBase.sol:127-132`).
* **The owner's `forward` of `CTM.upgradeChainFromVersion(id, old)`**
  (`ULabel.x (.forward [.sys (.transition id)])`), since `forward` reaches every CTM owner method
  (`governance/UpgradeExecutorBase.sol:35-55`).

## Modelling choices

* **Everything else is `ExecutorForward`'s model, unchanged.** `ULabel.x l` is `XStep` for every
  executor label except `XLabel.upgradeChain`, which this topic replaces by `ULabel.upgradeChain`
  and `ULabel.adminUpgrade`.
* **`upgradeChain(t, id)`** succeeds exactly when: `t` is nonzero (a call to address zero
  reverts: there is no code and the getter's return data cannot be decoded); the CTM commits `t`
  at the slot `t` reports (`CTMUpgradeExecutor.sol:99-102`); the chain is at that version (`Admin.sol:570-572`); and the
  chain then crosses its edge (`Step.transition`). The event's version is `t.newProtocolVersion()`.
* **The direct admin call** `Admin.upgradeChainFromVersion(_, old)` is `Step.transition` for a chain
  at version `old`.
* **Callers are not modelled**: every step admits every caller, and the owner/admin check of
  `upgradeChain` (`CTMUpgradeExecutor.sol:93-95`) only rejects. So the results that say a step does **not** exist hold for
  every caller, and those that say a step exists are for an authorized caller.
* **Timing is not modelled.** It does not separate the three paths: all of them run the same
  engine, so all face the same manifest `upgradeTimestamp` gate
  (`upgrades/BaseZkSyncUpgrade.sol:82-84`), all-batches-executed check
  (`upgrades/DefaultUpgrade.sol:30`) and settlement-layer order (`BaseZkSyncUpgrade.sol:89-94`),
  and none faces the chain's ServerNotifier gate, which the chain admin and the CTM are both
  exempt from (`Admin.sol:577`).
* **Validators** may also call `Admin.upgradeChainFromVersion`, subject to the ServerNotifier gate
  (`Admin.sol:577-585`). That is `ULabel.adminUpgrade` plus a rejecting check, so it is not a
  separate label.
-/

namespace Contracts.ChainTypeManager

/-- `ExecutorForward`'s label for the executor's `upgradeChain`, which this topic refines. -/
def XLabel.IsUpgradeChain : XLabel → Prop
  | .upgradeChain _ => True
  | _ => False

/-- What happens: `ExecutorForward`'s transactions, with the executor's `upgradeChain` carrying
its transition argument, and the chain admin's own call. -/
inductive ULabel
  /-- An `ExecutorForward` transaction other than `XLabel.upgradeChain`:
  `applyInfrastructureUpgrade`, `applyCTMUpgrade`, `forward`, or another actor's step. -/
  | x (l : XLabel)
  /-- `CTMUpgradeExecutor.upgradeChain(t, id)`. -/
  | upgradeChain (t : Address) (id : ChainId)
  /-- Chain `id`'s admin calling `Admin.upgradeChainFromVersion(_, old)` on its own diamond. -/
  | adminUpgrade (id : ChainId) (old : ℕ)

/-- One successful transaction. -/
inductive UStep (X : XConfig) : XState → ULabel → XState → Prop
  /-- Every other transaction and other actors' steps, exactly as in `ExecutorForward`. -/
  | x {s s' : XState} {l : XLabel} :
      ¬ l.IsUpgradeChain → XStep X s l s' → UStep X s (.x l) s'
  /-- `upgradeChain(t, id)` (`CTMUpgradeExecutor.sol:92-107`): `t.oldProtocolVersion()` is read
  (:96), `upgradeTransition` at that version must be `t` (:99-102), the CTM passes that version to
  the chain (:105, `ChainTypeManager.sol:618-621`), which must be at it (`Admin.sol:570-572`), and
  the chain crosses its edge. -/
  | upgradeChain {s : XState} {t : Address} {id : ChainId} {c : Chain} {sys' : Sys} :
      t ≠ 0 →
      s.sys.ctm.ut (X.W.tr t).old = t →
      s.sys.chains id = some c →
      c.pv = (X.W.tr t).old →
      Step X.W s.sys (.transition id) sys' →
      UStep X s (.upgradeChain t id) { s with sys := sys' }
  /-- The chain admin's `Admin.upgradeChainFromVersion(_, old)` (`Admin.sol:559-590`): the chain
  must be at `old` (:570-572); the admin is exempt from the ServerNotifier gate (:577). -/
  | adminUpgrade {s : XState} {id : ChainId} {old : ℕ} {c : Chain} {sys' : Sys} :
      s.sys.chains id = some c →
      c.pv = old →
      Step X.W s.sys (.transition id) sys' →
      UStep X s (.adminUpgrade id old) { s with sys := sys' }

/-- A sequence of successful transactions. -/
inductive URun (X : XConfig) : XState → List ULabel → XState → Prop
  | nil {s : XState} : URun X s [] s
  | cons {s s' s'' : XState} {u : ULabel} {us : List ULabel} :
      UStep X s u s' → URun X s' us s'' → URun X s (u :: us) s''

/-- The `ExecutorForward` label a transaction projects to. `ExecutorForward` has one label for a
chain crossing its edge, `XLabel.upgradeChain`, whose step is the bare `Step.transition`; both
refined ways of crossing project to it. This is a simulation map, used to carry
`ExecutorForward`'s results over; it does not say the two calls are the same entry point. -/
def ULabel.toX : ULabel → XLabel
  | .x l => l
  | .upgradeChain _ id => .upgradeChain id
  | .adminUpgrade id _ => .upgradeChain id

/-- The other direction, for governance: an `ExecutorForward` transaction as a refined one that
does not use the executor's `upgradeChain`. A crossing becomes the owner's `forward` of
`CTM.upgradeChainFromVersion`; every other transaction stays as it is. -/
def ULabel.ofX : XLabel → ULabel
  | .upgradeChain id => .x (.forward [.sys (.transition id)])
  | l => .x l

/-- A tame transaction, as in `ExecutorForward`: no infrastructure row names the CTM proxy, and
no forwarded call is a break-glass cut or a CTM code swap. Crossing an edge is always tame. -/
def ULabel.Tame (X : XConfig) (u : ULabel) : Prop := u.toX.Tame X

/-- `replaceUpgradeTransition(e, r)` is one of the calls a transaction forwards. -/
def XLabel.ForwardsReplace (e r : Address) : XLabel → Prop
  | .forward calls => FCall.sys (.ctm (.replace e r)) ∈ calls
  | _ => False

/-- `replaceUpgradeTransition(e, r)` is one of the calls a transaction forwards. -/
def ULabel.ForwardsReplace (e r : Address) (u : ULabel) : Prop := u.toX.ForwardsReplace e r

/-- Every committed slot holds a transition that reports that slot as its
`oldProtocolVersion()`. -/
def SlotsReport (W : World) (c : CTM) : Prop :=
  ∀ v, c.ut v ≠ 0 → (W.tr (c.ut v)).old = v

end Contracts.ChainTypeManager
