import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: `TransitionaryOwner` and one `Ownable2Step` target

Source: era-contracts `draft/v0.35.0`, commit `d9f678900e1bc8286412b78f56d4a9f443983c29`,
`l1-contracts/contracts/governance/TransitionaryOwner.sol` (23 lines), and OpenZeppelin v4
`access/Ownable2Step.sol` / `access/Ownable.sol` (the target's ownership logic).

**This file is definitions only.** Statements are in
`EraSpec.Contracts.TransitionaryOwner.Properties.Model`, proofs in
`EraSpec.Contracts.TransitionaryOwner.Proofs.Model`.

## The source

    contract TransitionaryOwner {
        address public immutable GOVERNANCE_ADDRESS;                               // :12
        constructor(address _governanceAddress) {                                  // :14
            GOVERNANCE_ADDRESS = _governanceAddress; }                             // :15
        function claimOwnershipAndGiveToGovernance(address target) external {      // :19
            Ownable2Step(target).acceptOwnership();                                // :20
            Ownable2Step(target).transferOwnership(GOVERNANCE_ADDRESS); }          // :21
    }

OpenZeppelin v4 `Ownable2Step`:

    function transferOwnership(address newOwner) public virtual override onlyOwner {
        _pendingOwner = newOwner; ... }                                            // :35-38
    function _transferOwnership(address newOwner) internal virtual override {
        delete _pendingOwner; super._transferOwnership(newOwner); }                // :44-47
    function acceptOwnership() public virtual {
        address sender = _msgSender();
        require(pendingOwner() == sender, "Ownable2Step: caller is not the new owner");
        _transferOwnership(sender); }                                              // :52-56

and `Ownable.renounceOwnership() onlyOwner { _transferOwnership(address(0)); }`.

## Modelling choices

* **One target.** The claim takes any `target`; the transitionary owner keeps no state, so a
  claim on another contract does not touch this one. The model follows one `Ownable2Step`
  target: its `owner` and `pendingOwner`.
* **The transitionary owner `TO` acts only through the claim.** It has no other function, so
  the target's entry points called with `msg.sender = TO` happen only inside the claim. The
  other labels require `caller ≠ TO`.
* **`msg.sender` is never the zero address**: every label requires `caller ≠ 0`.
* **A revert is the absence of a step.** The claim's two calls run in one transaction; if
  either reverts, the claim has no step.
* **Ghost counters.** `claims` counts successful claims; `nominations` counts
  `transferOwnership(TO)` calls on the target. They are not contract storage.
-/

namespace Contracts.TransitionaryOwner

open Clear

/-- Addresses as 256-bit words; `0` is the zero address. -/
abbrev Address := UInt256

/-- Fixed configuration: the transitionary owner's address and its immutable
`GOVERNANCE_ADDRESS` (`TransitionaryOwner.sol:12-16`). The constructor does not check `G`. -/
structure Config where
  /-- The address of the deployed `TransitionaryOwner`. -/
  TO : Address
  /-- `GOVERNANCE_ADDRESS`. -/
  G : Address

/-- The target's ownership storage plus two ghost counters. -/
structure State where
  /-- `Ownable._owner`. -/
  owner : Address
  /-- `Ownable2Step._pendingOwner`. -/
  pending : Address
  /-- Ghost: successful `claimOwnershipAndGiveToGovernance(target)` calls. -/
  claims : ℕ
  /-- Ghost: `transferOwnership(TO)` calls on the target. -/
  nominations : ℕ

/-- Transactions touching the target. -/
inductive Label where
  /-- `target.transferOwnership(newOwner)` sent by `caller` (not `TO`). -/
  | transfer (caller newOwner : Address)
  /-- `target.acceptOwnership()` sent by `caller` (not `TO`). -/
  | accept (caller : Address)
  /-- `target.renounceOwnership()` sent by `caller` (not `TO`). -/
  | renounce (caller : Address)
  /-- `TransitionaryOwner.claimOwnershipAndGiveToGovernance(target)` sent by anyone. -/
  | claim (caller : Address)

/-- One successful transaction. -/
inductive Step (K : Config) : State → Label → State → Prop where
  /-- `Ownable2Step.transferOwnership` (`:35-38`), `onlyOwner`. -/
  | transfer {s : State} {caller newOwner : Address} :
      caller ≠ 0 → caller ≠ K.TO → caller = s.owner →
      Step K s (.transfer caller newOwner)
        { s with pending := newOwner,
                 nominations := if newOwner = K.TO then s.nominations + 1 else s.nominations }
  /-- `Ownable2Step.acceptOwnership` (`:52-56`): `pendingOwner() == sender`, then
  `_transferOwnership(sender)` deletes the nomination. -/
  | accept {s : State} {caller : Address} :
      caller ≠ 0 → caller ≠ K.TO → s.pending = caller →
      Step K s (.accept caller) { s with owner := caller, pending := 0 }
  /-- `Ownable.renounceOwnership`, `onlyOwner`: `_transferOwnership(address(0))`. -/
  | renounce {s : State} {caller : Address} :
      caller ≠ 0 → caller ≠ K.TO → caller = s.owner →
      Step K s (.renounce caller) { s with owner := 0, pending := 0 }
  /-- `claimOwnershipAndGiveToGovernance` (`TransitionaryOwner.sol:19-22`): the target's
  `acceptOwnership()` with `msg.sender = TO` (requires `pendingOwner == TO`, makes `TO` the
  owner, clears the nomination), then `transferOwnership(G)` with `msg.sender = TO` (passes
  `onlyOwner`, sets `pendingOwner = G`). -/
  | claim {s : State} {caller : Address} :
      caller ≠ 0 → s.pending = K.TO →
      Step K s (.claim caller)
        { s with owner := K.TO, pending := K.G, claims := s.claims + 1 }

/-- Reachability from `s₀` along any sequence of successful transactions. -/
inductive Reach (K : Config) (s₀ : State) : State → Prop where
  | refl : Reach K s₀ s₀
  | step {s s' : State} {l : Label} : Reach K s₀ s → Step K s l s' → Reach K s₀ s'

/-- A run: the labels in order. -/
inductive Run (K : Config) : State → List Label → State → Prop where
  | nil (s : State) : Run K s [] s
  | cons {s s' s'' : State} {l : Label} {ls : List Label} :
      Step K s l s' → Run K s' ls s'' → Run K s (l :: ls) s''

/-- A fresh target: owned by `o`, no nomination, ghost counters at zero. -/
def fresh (o : Address) : State := ⟨o, 0, 0, 0⟩

/-! ## Countermodel: the target's `pendingOwner` check removed -/

/-- The claim against a target whose `acceptOwnership()` does **not** check
`pendingOwner() == msg.sender` (the `require` at `Ownable2Step.sol:54` deleted). -/
inductive UncheckedClaim (K : Config) : State → State → Prop where
  | claim {s : State} : UncheckedClaim K s
      { s with owner := K.TO, pending := K.G, claims := s.claims + 1 }

end Contracts.TransitionaryOwner
