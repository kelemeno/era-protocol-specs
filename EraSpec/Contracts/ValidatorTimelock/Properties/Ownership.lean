import EraSpec.Contracts.ValidatorTimelock.Specs.Model
import EraSpec.Core.Headline

/-!
# Properties: initialization and the owner

Statements about `EraSpec.Contracts.ValidatorTimelock.Specs.Model` (source `b17415d20`, with
OpenZeppelin `contracts-upgradeable` v4.9.6). Proofs are in
`EraSpec.Contracts.ValidatorTimelock.Proofs.Ownership`.

* **`initialize` runs at most once** along any run, and not at all from initialized storage
  (`InitializeAtMostOnce`).
* **The owner changes only by the two-step handover, renouncing, or `initialize`**
  (`OwnerChangesOnlyByHandover`): `acceptOwnership` by the pending owner, `renounceOwnership`
  by the owner (to `0`), or `initialize` on uninitialized storage. The pending owner changes
  only by the owner's `transferOwnership` or is cleared to `0`.
* **The owner-only calls** (`OwnerOnlyCalls`): `transferOwnership`, `renounceOwnership`,
  `setExecutionDelay` and `setChainExecutionDelay` succeed only for the owner.
* **A renounced timelock's delays only rise** (`RenouncedTimelockOnlyRaisesDelays`): once
  initialized storage has owner `0` and no pending owner, along any run in which no call is
  sent by address `0`, the owner stays `0`, the ecosystem-wide delay never changes, and the
  delay enforced for every chain never falls.
* **The sender premise is needed in the model** (`ZeroSenderActsAsRenouncedOwner`): `msg.sender`
  is any word in the model, and a call "from `0`" passes `onlyOwner` once the owner is `0`. On a
  real chain no call has sender `0`.

`HandoverWitness` and `RenounceWitness` instantiate the premises.
-/

namespace Contracts.ValidatorTimelock

/-- **`initialize` RUNS AT MOST ONCE.** Along any run of successful calls, at most one is
`initialize`; none is if the run starts initialized; and the run ends initialized if one is. -/
@[headline] def Properties.InitializeAtMostOnce : Prop :=
  ∀ (s s' : State) (ks : List Call), Run s ks s' →
    (ks.filter (fun k => k.action.isInitialize)).length ≤ 1 ∧
    (s.initialized = true → ks.filter (fun k => k.action.isInitialize) = []) ∧
    (ks.filter (fun k => k.action.isInitialize) ≠ [] → s'.initialized = true)

/-- **THE OWNER CHANGES ONLY BY HANDOVER, RENOUNCING OR `initialize`.** If a successful call
changes the owner, it is `initialize` (with the new owner as argument) on uninitialized storage,
`acceptOwnership` sent by the pending owner (who becomes the owner), or `renounceOwnership` sent
by the owner (the owner becomes `0`). If it changes the pending owner, it is the owner's
`transferOwnership` to the new pending owner, or the pending owner becomes `0`. -/
@[headline] def Properties.OwnerChangesOnlyByHandover : Prop :=
  ∀ (k : Call) (s s' : State), step k s = some s' →
    (s'.owner ≠ s.owner →
      (∃ d, k.action = .initializeTimelock s'.owner d ∧ s.initialized = false) ∨
      (k.action = .acceptOwnership ∧ k.sender = s.pendingOwner ∧ s'.owner = k.sender) ∨
      (k.action = .renounceOwnership ∧ k.sender = s.owner ∧ s'.owner = 0)) ∧
    (s'.pendingOwner ≠ s.pendingOwner →
      (∃ n, k.action = .transferOwnership n ∧ k.sender = s.owner ∧ s'.pendingOwner = n) ∨
      s'.pendingOwner = 0)

/-- **THE OWNER-ONLY CALLS.** A successful `transferOwnership`, `renounceOwnership`,
`setExecutionDelay` or `setChainExecutionDelay` was sent by the owner. -/
def Properties.OwnerOnlyCalls : Prop :=
  ∀ (k : Call) (s s' : State), step k s = some s' →
    (k.action = .renounceOwnership ∨ (∃ n, k.action = .transferOwnership n) ∨
      (∃ d, k.action = .setExecutionDelay d) ∨ (∃ c d, k.action = .setChainExecutionDelay c d)) →
    k.sender = s.owner

/-- **A RENOUNCED TIMELOCK'S DELAYS ONLY RISE.** Start from initialized storage with owner `0`
and pending owner `0`. Along any run of successful calls none of which is sent by address `0`,
the owner and the pending owner stay `0`, the ecosystem-wide delay is unchanged, and the delay
enforced for every chain at the end is at least the one at the start. -/
@[headline] def Properties.RenouncedTimelockOnlyRaisesDelays : Prop :=
  ∀ (s s' : State) (ks : List Call), s.initialized = true → s.owner = 0 → s.pendingOwner = 0 →
    (∀ k ∈ ks, k.sender ≠ 0) → Run s ks s' →
    s'.owner = 0 ∧ s'.pendingOwner = 0 ∧ s'.executionDelay = s.executionDelay ∧
      ∀ c, enforcedDelay s c ≤ enforcedDelay s' c

/-- **IN THE MODEL, SENDER `0` ACTS AS A RENOUNCED OWNER.** After the witness setup, the owner
renounces; a call with sender `0` then succeeds with `setExecutionDelay(0)`, lowering the
ecosystem delay from `100` to `0`. So the sender premise of `RenouncedTimelockOnlyRaisesDelays`
cannot be dropped from the model's statement. -/
@[countermodel] def Properties.ZeroSenderActsAsRenouncedOwner : Prop :=
  ∃ s₀ s₁ s₂ : State,
    Run init vtSetupCalls s₀ ∧ step (vtCall 1 vtOwner .renounceOwnership) s₀ = some s₁ ∧
    s₁.owner = 0 ∧ s₁.executionDelay = 100 ∧
    step (vtCall 2 0 (.setExecutionDelay 0)) s₁ = some s₂ ∧ s₂.executionDelay = 0

/-! ## Witnesses -/

/-- **THE TWO-STEP HANDOVER RUNS.** After the witness setup (owner `1`), `1` calls
`transferOwnership(7)`, `7` accepts and becomes the owner with no pending owner, and a second
`initialize` reverts. -/
@[witness] def Properties.HandoverWitness : Prop :=
  ∃ s₀ s₁ s₂ : State,
    Run init vtSetupCalls s₀ ∧ s₀.owner = vtOwner ∧ s₀.initialized = true ∧
    step (vtCall 1 vtOwner (.transferOwnership 7)) s₀ = some s₁ ∧ s₁.pendingOwner = 7 ∧
    step (vtCall 2 7 .acceptOwnership) s₁ = some s₂ ∧ s₂.owner = 7 ∧ s₂.pendingOwner = 0 ∧
    step (vtCall 3 7 (.initializeTimelock 7 0)) s₂ = none

/-- **A RENOUNCED TIMELOCK STILL RUNS.** After the witness setup the owner renounces: storage is
initialized with owner and pending owner `0`. The chain admin's
`increaseChainExecutionDelay(100, 200)` then succeeds (sender `2`), raising the delay enforced
for chain `100` from `100` to `200`, and the former owner's `setExecutionDelay(0)` reverts. -/
@[witness] def Properties.RenounceWitness : Prop :=
  ∃ s₀ s₁ s₂ : State,
    Run init vtSetupCalls s₀ ∧ step (vtCall 1 vtOwner .renounceOwnership) s₀ = some s₁ ∧
    s₁.initialized = true ∧ s₁.owner = 0 ∧ s₁.pendingOwner = 0 ∧
    Run s₁ [vtCall 2 vtAdmin (.increaseChainExecutionDelay vtChain 200)] s₂ ∧ vtAdmin ≠ 0 ∧
    enforcedDelay s₁ vtChain = 100 ∧ enforcedDelay s₂ vtChain = 200 ∧
    step (vtCall 3 vtOwner (.setExecutionDelay 0)) s₂ = none

end Contracts.ValidatorTimelock
