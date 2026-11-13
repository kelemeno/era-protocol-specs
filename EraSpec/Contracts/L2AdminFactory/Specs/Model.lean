import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: `L2AdminFactory.deployAdmin` and the `ChainAdmin` constructor it runs

Source: era-contracts `draft/v0.35.0`, commit `d9f678900e1bc8286412b78f56d4a9f443983c29`,
paths under `l1-contracts/contracts/`: `governance/L2AdminFactory.sol` (69 lines), the slice of
`governance/ChainAdmin.sol` its `new ChainAdmin(...)` executes (constructor :45-51,
`_addRestriction` :119-126), and `governance/restriction/RestrictionValidator.sol:17-21`.

**This file is definitions only.** Statements are in
`EraSpec.Contracts.L2AdminFactory.Properties.Model`, proofs in
`EraSpec.Contracts.L2AdminFactory.Proofs.Model`.

## The source

    address[] public requiredRestrictions;                                      // :22
    constructor(address[] memory _requiredRestrictions) {
        _validateRestrictions(_requiredRestrictions);                           // :25
        requiredRestrictions = _requiredRestrictions; }                         // :26
    function deployAdmin(address[] memory _additionalRestrictions) external returns (address admin) {
        _validateRestrictions(_additionalRestrictions);                         // :35
        ... restrictions = requiredRestrictions ++ _additionalRestrictions      // :36-47
        admin = address(new ChainAdmin(restrictions));                          // :53 (CREATE)
        emit AdminDeployed(address(admin)); }                                   // :55
    function _validateRestrictions(address[] memory _restrictions) internal view {
        for (...) RestrictionValidator.validateRestriction(_restrictions[i]); } // :61-68

`ChainAdmin`:

    constructor(address[] memory _initialRestrictions) reentrancyGuardInitializer {
        for (...) _addRestriction(_initialRestrictions[i]); }                   // :45-51
    function _addRestriction(address _restriction) private {
        RestrictionValidator.validateRestriction(_restriction);                 // :120
        if (!activeRestrictions.add(_restriction)) {
            revert RestrictionWasAlreadyPresent(_restriction); } ... }          // :122-124

`validateRestriction` requires `getSupportsRestrictionMagic() == RESTRICTION_MAGIC`
(`RestrictionValidator.sol:17-21`).

## Modelling choices

* **`requiredRestrictions` is configuration** (`Config.required`): no function writes it after
  the constructor (the contract is described as immutable, :14-15).
* **The validator's verdict is an environment view per transaction** (`Validity`): the
  restriction's `getSupportsRestrictionMagic()` is external code, so the model lets the answer
  differ from one transaction to the next. A call that reverts counts as `false`.
* **`CREATE` addresses** are `Config.createAddr n`, the address `new` yields at factory
  nonce `n`; the nonce goes up by one per deployment. No injectivity of `createAddr` is
  assumed; results about distinct addresses are stated in collision form.
* **The deployed admin** is logged as `AdminRec`: its address, the nonce used, and its
  initial `activeRestrictions`, in insertion order. The rest of `ChainAdmin` is not modelled
  (`ChainAdmin` itself belongs to another model).
* **A revert is the absence of a step.**
-/

namespace Contracts.L2AdminFactory

open Clear

/-- Addresses as 256-bit words. -/
abbrev Address := UInt256

/-- The validator's verdict on each address in one transaction. -/
abbrev Validity := Address → Bool

/-- Fixed configuration. -/
structure Config where
  /-- `requiredRestrictions`, in order. -/
  required : List Address
  /-- The address `CREATE` yields at factory nonce `n`. -/
  createAddr : ℕ → Address

/-- One deployed admin, as the factory left it. -/
structure AdminRec where
  /-- The new `ChainAdmin`'s address. -/
  addr : Address
  /-- The factory nonce used. -/
  nonce : ℕ
  /-- Its initial `activeRestrictions`, in insertion order. -/
  restrictions : List Address

/-- The factory's nonce and the log of admins it deployed (oldest first). -/
structure State where
  /-- The factory account's `CREATE` nonce. -/
  nonce : ℕ
  /-- Ghost: every admin deployed so far. -/
  admins : List AdminRec

/-- `deployAdmin(additional)` under validator verdicts `v`. -/
structure Label where
  /-- The validator's verdicts during the transaction. -/
  v : Validity
  /-- `_additionalRestrictions`. -/
  additional : List Address

/-- `ChainAdmin`'s constructor succeeds on `rs`: every `_addRestriction` validates
(`:120`) and inserts a new element (`:122-124`). -/
def ChainAdminCtorOk (v : Validity) (rs : List Address) : Prop :=
  (∀ r ∈ rs, v r = true) ∧ rs.Nodup

/-- The state after a successful deployment. -/
def deployed (K : Config) (s : State) (add : List Address) : State :=
  { nonce := s.nonce + 1,
    admins := s.admins ++ [⟨K.createAddr s.nonce, s.nonce, K.required ++ add⟩] }

/-- One successful `deployAdmin` (`L2AdminFactory.sol:32-56`). -/
inductive Step (K : Config) : State → Label → State → Prop where
  | deploy {s : State} {v : Validity} {add : List Address} :
      /- `_validateRestrictions(_additionalRestrictions)`, :35 -/
      (∀ r ∈ add, v r = true) →
      /- `new ChainAdmin(required ++ additional)`, :53 -/
      ChainAdminCtorOk v (K.required ++ add) →
      Step K s ⟨v, add⟩ (deployed K s add)

/-- Reachability along any sequence of deployments. -/
inductive Reach (K : Config) (s₀ : State) : State → Prop where
  | refl : Reach K s₀ s₀
  | step {s s' : State} {l : Label} : Reach K s₀ s → Step K s l s' → Reach K s₀ s'

/-! ## Variants (for the redundancy and countermodel results) -/

/-- `deployAdmin` with the factory's own `_validateRestrictions` (:35) deleted. -/
inductive StepNoFactoryCheck (K : Config) : State → Label → State → Prop where
  | deploy {s : State} {v : Validity} {add : List Address} :
      ChainAdminCtorOk v (K.required ++ add) →
      StepNoFactoryCheck K s ⟨v, add⟩ (deployed K s add)

/-- `deployAdmin` with both validations deleted (factory :35 and `ChainAdmin` :120); only
the duplicate check remains. -/
inductive StepNoValidation (K : Config) : State → Label → State → Prop where
  | deploy {s : State} {v : Validity} {add : List Address} :
      (K.required ++ add).Nodup →
      StepNoValidation K s ⟨v, add⟩ (deployed K s add)

end Contracts.L2AdminFactory
