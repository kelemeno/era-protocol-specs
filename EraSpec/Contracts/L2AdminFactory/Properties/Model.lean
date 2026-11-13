import EraSpec.Contracts.L2AdminFactory.Specs.Model

/-!
# Properties: every admin the factory deploys carries the required restrictions

Statements about `EraSpec.Contracts.L2AdminFactory.Specs.Model`; proofs in
`EraSpec.Contracts.L2AdminFactory.Proofs.Model`.

* `DeploySucceedsIff`: `deployAdmin(add)` succeeds exactly when every restriction of
  `required ++ add` passes the validator and the list has no duplicates.
* `EveryAdminHasRequired` (run-level): every deployed admin starts with the required
  restrictions as a prefix, has no duplicate, sits at the `CREATE` address of its nonce, and
  used a nonce below the current one.
* `AdminsDistinctOrCreateCollision` (run-level): deployed admins have pairwise distinct
  addresses, unless `CREATE` maps two of the nonces used to one address.
* `DeployedRestrictionsValid`: each restriction of a new admin passed the validator in that
  transaction.
* `DuplicateRequiredBricksFactory` (source observation): the constructor does not check
  `required` for duplicates; with one, every `deployAdmin` reverts.
* `FactoryCheckRedundant`: the factory's own check (:35) changes no outcome; `ChainAdmin`'s
  constructor re-checks every restriction.
* `UnvalidatedAdminAdmitsAnything` (countermodel): with both checks deleted, an admin is
  deployed with a restriction the validator rejects.
* `DeployWitness`: a concrete deployment.
-/

namespace Contracts.L2AdminFactory

/-- **WHEN `deployAdmin` SUCCEEDS.** A `deployAdmin(add)` step exists exactly when every
address of `requiredRestrictions ++ add` passes the validator in that transaction and that
list has no duplicate. -/
def Properties.DeploySucceedsIff : Prop :=
  ∀ (K : Config) (s : State) (v : Validity) (add : List Address),
    (∃ s', Step K s ⟨v, add⟩ s') ↔ ((∀ r ∈ K.required ++ add, v r = true) ∧ (K.required ++ add).Nodup)

/-- **EVERY DEPLOYED ADMIN CARRIES THE REQUIRED RESTRICTIONS.** Along any run from a state
with no deployed admins, every logged admin's initial restrictions have
`requiredRestrictions` as a prefix and no duplicate; its address is `createAddr` of its nonce;
its nonce is below the factory's current nonce and at least the starting nonce. -/
def Properties.EveryAdminHasRequired : Prop :=
  ∀ (K : Config) (n₀ : ℕ) (s : State), Reach K ⟨n₀, []⟩ s → ∀ a ∈ s.admins,
    K.required <+: a.restrictions ∧ a.restrictions.Nodup ∧ a.addr = K.createAddr a.nonce ∧
      n₀ ≤ a.nonce ∧ a.nonce < s.nonce

/-- **DEPLOYED ADMINS ARE DISTINCT, OR `CREATE` COLLIDES.** Along any run from a state with no
deployed admins, either the logged admin addresses are pairwise distinct, or two different
nonces `n < m` among those used (`n₀ ≤ n`, `m < s.nonce`) have the same `CREATE` address. -/
def Properties.AdminsDistinctOrCreateCollision : Prop :=
  ∀ (K : Config) (n₀ : ℕ) (s : State), Reach K ⟨n₀, []⟩ s →
    (s.admins.map AdminRec.addr).Nodup ∨
      ∃ n m, n₀ ≤ n ∧ n < m ∧ m < s.nonce ∧ K.createAddr n = K.createAddr m

/-- **A NEW ADMIN'S RESTRICTIONS PASSED THE VALIDATOR.** After `deployAdmin(add)` under
verdicts `v`, every restriction of the newly logged admin has `v r = true`. -/
def Properties.DeployedRestrictionsValid : Prop :=
  ∀ (K : Config) (s s' : State) (v : Validity) (add : List Address),
    Step K s ⟨v, add⟩ s' → ∀ r ∈ K.required ++ add, v r = true

/-- **OBSERVATION: A DUPLICATE REQUIRED RESTRICTION BRICKS THE FACTORY.** The constructor
validates `requiredRestrictions` but does not check duplicates (`L2AdminFactory.sol:24-27`);
`ChainAdmin` rejects them (`ChainAdmin.sol:122-124`). With a duplicate, no `deployAdmin`
succeeds, whatever the arguments. -/
def Properties.DuplicateRequiredBricksFactory : Prop :=
  ∀ (K : Config) (s s' : State) (l : Label), ¬ K.required.Nodup → ¬ Step K s l s'

/-- **THE FACTORY'S OWN CHECK IS REDUNDANT.** Deleting `_validateRestrictions` at :35
changes no step: `ChainAdmin`'s constructor validates every restriction (`:120`), as the
source comment at :33-34 says. -/
def Properties.FactoryCheckRedundant : Prop :=
  ∀ (K : Config) (s s' : State) (l : Label), Step K s l s' ↔ StepNoFactoryCheck K s l s'

/-- **COUNTERMODEL: VALIDATION IS LOAD-BEARING.** With both validations deleted, a
deployment succeeds with a required restriction that the validator rejects in that
transaction. -/
def Properties.UnvalidatedAdminAdmitsAnything : Prop :=
  ∃ (K : Config) (s s' : State) (l : Label),
    StepNoValidation K s l s' ∧ (∃ r ∈ K.required, l.v r = false) ∧ ¬ Step K s l s'

/-- **WITNESS.** Required `[7]`, additional `[8]`, all valid: an admin at `createAddr 0`
with restrictions `[7, 8]` is deployed. -/
def Properties.DeployWitness : Prop :=
  ∃ s : State, Reach ⟨[7], fun n => (n : Address) + 100⟩ ⟨0, []⟩ s ∧
    s.admins = [⟨100, 0, [7, 8]⟩] ∧ s.nonce = 1

end Contracts.L2AdminFactory
