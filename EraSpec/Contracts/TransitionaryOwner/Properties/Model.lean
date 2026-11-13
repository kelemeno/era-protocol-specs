import EraSpec.Contracts.TransitionaryOwner.Specs.Model

/-!
# Properties: the transitionary owner hands ownership on, once per nomination

Statements about `EraSpec.Contracts.TransitionaryOwner.Specs.Model`; proofs in
`EraSpec.Contracts.TransitionaryOwner.Proofs.Model`.

* `ClaimHandsToGovernance`: a successful claim needs `TO` nominated and leaves `TO` owner
  with governance nominated.
* `NeverParkedWithoutGovernanceNominee` (run-level): whenever `TO` owns the target,
  governance is the nominee.
* `ClaimsBoundedByNominations` (run-level): every successful claim consumes one nomination
  of `TO`; from a fresh target, claims never exceed nominations.
* `SecondClaimFails`: right after a claim, no claim succeeds.
* `ZeroGovernanceStrandsOwnership` (source finding, deploy-time): with
  `GOVERNANCE_ADDRESS = 0` (the constructor does not check it), a claim leaves the target
  owned by `TO` forever.
* `UncheckedClaimTakesOwnership` (countermodel): without the target's
  `pendingOwner == msg.sender` check, a claim takes a target nobody nominated `TO` on.
* `HandoffWitness`: nominate `TO`, claim, governance accepts.
-/

namespace Contracts.TransitionaryOwner

/-- **A CLAIM NEEDS `TO` NOMINATED AND HANDS ON TO GOVERNANCE.** Any successful
`claimOwnershipAndGiveToGovernance(target)`, whoever sends it, requires `pendingOwner = TO`
before, and leaves `owner = TO`, `pendingOwner = GOVERNANCE_ADDRESS`, one more claim. -/
def Properties.ClaimHandsToGovernance : Prop :=
  ∀ (K : Config) (s s' : State) (c : Address), Step K s (.claim c) s' →
    s.pending = K.TO ∧ s'.owner = K.TO ∧ s'.pending = K.G ∧ s'.claims = s.claims + 1

/-- **`TO` NEVER HOLDS THE TARGET WITHOUT GOVERNANCE NOMINATED.** If `TO ≠ 0`,
`GOVERNANCE_ADDRESS ≠ TO`, and the start state is not owned by `TO` (or already has governance
nominated), then in every state reachable by any interleaving of transfers, accepts,
renounces and claims, `owner = TO` implies `pendingOwner = GOVERNANCE_ADDRESS`. -/
def Properties.NeverParkedWithoutGovernanceNominee : Prop :=
  ∀ (K : Config) (s₀ s : State), K.TO ≠ 0 → K.G ≠ K.TO →
    (s₀.owner = K.TO → s₀.pending = K.G) → Reach K s₀ s →
    s.owner = K.TO → s.pending = K.G

/-- **ONE CLAIM PER NOMINATION.** If `TO ≠ 0` and `GOVERNANCE_ADDRESS ≠ TO`, then along any
run from a fresh target (any owner, no nomination), the successful claims plus one for an
outstanding nomination of `TO` never exceed the `transferOwnership(TO)` calls. -/
def Properties.ClaimsBoundedByNominations : Prop :=
  ∀ (K : Config) (o : Address) (s : State), K.TO ≠ 0 → K.G ≠ K.TO →
    Reach K (fresh o) s → s.claims + (if s.pending = K.TO then 1 else 0) ≤ s.nominations

/-- **A CLAIM CANNOT BE REPEATED.** If `GOVERNANCE_ADDRESS ≠ TO`, then right after a
successful claim, no claim (by anyone) succeeds. -/
def Properties.SecondClaimFails : Prop :=
  ∀ (K : Config) (s s' s'' : State) (c c' : Address), K.G ≠ K.TO →
    Step K s (.claim c) s' → ¬ Step K s' (.claim c') s''

/-- **SOURCE FINDING: ZERO GOVERNANCE STRANDS THE TARGET.** The constructor accepts
`GOVERNANCE_ADDRESS = 0` (`TransitionaryOwner.sol:14-16`) and OpenZeppelin's
`transferOwnership(0)` only clears the nomination. Then, if `TO ≠ 0`, after a successful claim
every reachable state has `owner = TO` and no nominee: `TO` has no function to move it on. -/
def Properties.ZeroGovernanceStrandsOwnership : Prop :=
  ∀ (K : Config) (s s' s'' : State) (c : Address), K.G = 0 → K.TO ≠ 0 →
    Step K s (.claim c) s' → Reach K s' s'' → s''.owner = K.TO ∧ s''.pending = 0

/-- **COUNTERMODEL: THE TARGET'S NOMINEE CHECK IS LOAD-BEARING.** Without
`require(pendingOwner() == sender)` (`Ownable2Step.sol:54`), a claim on a fresh target owned by
someone else, with no nomination, makes `TO` the owner: more claims than nominations, which
`ClaimsBoundedByNominations` excludes for the real target. -/
def Properties.UncheckedClaimTakesOwnership : Prop :=
  ∃ (K : Config) (o : Address) (s' : State), K.TO ≠ 0 ∧ K.G ≠ K.TO ∧ o ≠ K.TO ∧
    UncheckedClaim K (fresh o) s' ∧ s'.owner = K.TO ∧ s'.nominations < s'.claims

/-- **WITNESS.** A fresh target owned by `1` nominates `TO = 2`, anyone claims, and
governance `3` accepts: governance owns the target, nothing is pending, one claim. -/
def Properties.HandoffWitness : Prop :=
  ∃ s : State, Reach ⟨2, 3⟩ (fresh 1) s ∧ s.owner = 3 ∧ s.pending = 0 ∧ s.claims = 1 ∧
    s.nominations = 1

end Contracts.TransitionaryOwner
