import EraSpec.Contracts.DataAvailability.Specs.RollupDAManager

/-!
# Properties: `RollupDAManager` — the allowed DA pairs change only by the owner

Statements about `EraSpec.Contracts.DataAvailability.Specs.RollupDAManager`. Proofs are in
`EraSpec.Contracts.DataAvailability.Proofs.RollupDAManager`.

Run-level (any interleaving of the four entry points, any callers):

* `PairsFollowOwnerUpdates` (headline): the allow-list at the end of a run is the initial one
  overwritten by the logged `updateDAPair` calls, each of which was made by the owner of that
  moment with a non-zero validator and a scheme other than `NONE`.
* `InvalidPairsNeverAllowed`: the zero validator and the `NONE` scheme are never allowed.
* `OwnerChangesOnlyByHandover`: the owner is the initial owner, or zero, or an address that an
  owner nominated and that then accepted.
* `OutsidersCannotAct`: a run in which nobody acts as the initial owner or the initial pending
  owner contains no successful call.
* `RenouncedManagerFrozen`: `renounceOwnership` is not disabled; after it the allow-list can never
  change again.

Countermodels and witness: `OwnerCheckLoadBearing`, `ValidConfigurationCheckLoadBearing`,
`ManagerRunWitness`.
-/

namespace Contracts.DataAvailability

/-- **HEADLINE: THE ALLOW-LIST IS EXACTLY WHAT THE OWNERS WROTE.** For every run of successful
calls from `M₀` to `M` with log `log`:

* for every pair `(v, s)`, `isPairAllowed(v, s)` at the end is the status written by the last
  logged `updateDAPair` on that pair, or the initial value if there is none;
* every logged `updateDAPair` was called by the owner of the state it ran in, with `v ≠ 0` and
  `s ≠ NONE`.

So no call other than an owner's `updateDAPair` changes any pair. -/
def Properties.PairsFollowOwnerUpdates : Prop :=
  ∀ (M₀ M : Manager) (log : List (Manager × MCall)), ReachLog M₀ M log →
    (∀ v s, M.allowed v s = (lastStatus log v s).getD (M₀.allowed v s))
    ∧ ∀ pre c v s st, (pre, MCall.updateDAPair c v s st) ∈ log →
        c = pre.owner ∧ v ≠ 0 ∧ s ≠ L2DACommitmentScheme.NONE

/-- **THE ZERO VALIDATOR AND THE `NONE` SCHEME ARE NEVER ALLOWED.** `NoInvalidPairs` is preserved
by every run, and it holds after deployment. So in every state reachable from a deployment,
`isPairAllowed(address(0), s)` and `isPairAllowed(v, NONE)` are `false`. -/
def Properties.InvalidPairsNeverAllowed : Prop :=
  (∀ (M₀ M : Manager), NoInvalidPairs M₀ → Reach M₀ M → NoInvalidPairs M)
  ∧ ∀ (deployer : Address) (M : Manager), Reach (deploy deployer) M → NoInvalidPairs M

/-- **THE OWNER CHANGES ONLY BY RENOUNCING OR BY A TWO-STEP HANDOVER.** After any run:

* the pending owner is zero or was nominated (`Nominated`: it was the initial pending owner, or the
  owner of the moment named it in a logged `transferOwnership`);
* the owner is the initial owner, or zero, or a nominated address that called `acceptOwnership`
  itself while it was the pending owner. -/
def Properties.OwnerChangesOnlyByHandover : Prop :=
  ∀ (M₀ M : Manager) (log : List (Manager × MCall)), ReachLog M₀ M log →
    (M.pendingOwner = 0 ∨ Nominated M₀ log M.pendingOwner)
    ∧ (M.owner = M₀.owner ∨ M.owner = 0
        ∨ (Nominated M₀ log M.owner
            ∧ ∃ pre, (pre, MCall.acceptOwnership M.owner) ∈ log ∧ pre.pendingOwner = M.owner))

/-- **OUTSIDERS CANNOT ACT.** If no call of a run is made by the initial owner or by the initial
pending owner, the run is empty: no call succeeded, and the whole state (owner, pending owner,
allow-list) is unchanged. -/
def Properties.OutsidersCannotAct : Prop :=
  ∀ (M₀ M : Manager) (log : List (Manager × MCall)), ReachLog M₀ M log →
    (∀ e ∈ log, e.2.caller ≠ M₀.owner ∧ e.2.caller ≠ M₀.pendingOwner) →
    log = [] ∧ M = M₀

/-- **A RENOUNCED MANAGER IS FROZEN FOR GOOD.** `renounceOwnership` is inherited from OpenZeppelin
and not disabled. A successful call sets the owner and the pending owner to zero (a pending
nomination is cancelled) and keeps the allow-list. From any state with zero owner and zero pending
owner, no call by a non-zero caller ever succeeds, so the allow-list stays as it is: no pair can be
added and none can be revoked. The premise `caller ≠ 0` is the EVM fact that no transaction or
contract call has `msg.sender = address(0)` (`VM-CALL`). -/
def Properties.RenouncedManagerFrozen : Prop :=
  (∀ (M M' : Manager) (c : Address), exec M (.renounceOwnership c) = some M' →
      c = M.owner ∧ M'.owner = 0 ∧ M'.pendingOwner = 0 ∧ M'.allowed = M.allowed)
  ∧ ∀ (M₀ M : Manager) (log : List (Manager × MCall)),
      M₀.owner = 0 → M₀.pendingOwner = 0 → ReachLog M₀ M log →
      (∀ e ∈ log, e.2.caller ≠ 0) → log = [] ∧ M = M₀

/-- **COUNTERMODEL: `onlyOwner` IS LOAD-BEARING.** There is a state and a caller that is neither
the owner nor the pending owner for which the source's `updateDAPair` reverts, while the same
function without `onlyOwner` (`updateDAPairNoOwner`) allows a pair that was not allowed. -/
def Properties.OwnerCheckLoadBearing : Prop :=
  ∃ (M M' : Manager) (c v : Address) (s : L2DACommitmentScheme),
    c ≠ M.owner ∧ c ≠ M.pendingOwner ∧ M.allowed v s = false
      ∧ exec M (.updateDAPair c v s true) = none
      ∧ updateDAPairNoOwner M v s true = some M' ∧ M'.allowed v s = true

/-- **COUNTERMODEL: `validDAConfiguration` IS LOAD-BEARING.** From a freshly deployed manager, the
owner's `updateDAPair` reverts on the zero validator and on the `NONE` scheme. Without the modifier
(`updateDAPairUnchecked`) each call succeeds and the result violates `NoInvalidPairs`. -/
def Properties.ValidConfigurationCheckLoadBearing : Prop :=
  ∃ (o v : Address) (s : L2DACommitmentScheme) (M₁ M₂ : Manager),
    v ≠ 0 ∧ s ≠ .NONE ∧ NoInvalidPairs (deploy o)
      ∧ exec (deploy o) (.updateDAPair o 0 s true) = none
      ∧ exec (deploy o) (.updateDAPair o v .NONE true) = none
      ∧ updateDAPairUnchecked (deploy o) o 0 s true = some M₁ ∧ ¬ NoInvalidPairs M₁
      ∧ updateDAPairUnchecked (deploy o) o v .NONE true = some M₂ ∧ ¬ NoInvalidPairs M₂

/-- **WITNESS: A RUN WITH AN UPDATE, A REVOCATION AND A HANDOVER.** From the deployment by address
`1`: the owner allows two pairs, nominates address `2`, which accepts and then revokes one pair.
At the end the owner is `2`, one pair is allowed and the other is not, the former owner's
`updateDAPair` reverts, and the new owner's succeeds. -/
def Properties.ManagerRunWitness : Prop :=
  ∃ (M M' : Manager) (log : List (Manager × MCall)),
    ReachLog (deploy 1) M log ∧ log.length = 5 ∧ M.owner = 2 ∧ M.pendingOwner = 0
      ∧ M.allowed 5 .BLOBS_AND_PUBDATA_KECCAK256 = true
      ∧ M.allowed 6 .PUBDATA_KECCAK256 = false
      ∧ lastStatus log 6 .PUBDATA_KECCAK256 = some false
      ∧ exec M (.updateDAPair 1 7 .EMPTY_NO_DA true) = none
      ∧ exec M (.updateDAPair 2 7 .EMPTY_NO_DA true) = some M'
      ∧ M'.allowed 7 .EMPTY_NO_DA = true

end Contracts.DataAvailability
