import EraSpec.Contracts.DataAvailability.Specs.Common

/-!
# Spec: `RollupDAManager` and its `Ownable2Step` owner

Source: era-contracts `d9f678900e1bc8286412b78f56d4a9f443983c29`,
`l1-contracts/contracts/state-transition/data-availability/RollupDAManager.sol` (79 lines), and the
OpenZeppelin v4 submodule it pins (`lib/openzeppelin-contracts-v4` at
`dc44c9f1a4c3b10af99492eed84f83ed244203f6`), files `contracts/access/Ownable.sol` and
`contracts/access/Ownable2Step.sol`.

The contract's whole storage is three slots:

* `Ownable._owner` and `Ownable2Step._pendingOwner`;
* `isAllowedDAConfiguration : address → L2DACommitmentScheme → bool` (`RollupDAManager.sol:22-23`).

Its non-view entry points are exactly four:

* `updateDAPair(l1DAValidator, scheme, status)` (`RollupDAManager.sol:58-66`): `onlyOwner`, then the
  `validDAConfiguration` modifier (`:34-43`: validator non-zero, scheme not `NONE`), then one write;
* `transferOwnership(newOwner)` (`Ownable2Step.sol:35-38`): `onlyOwner`, sets the pending owner (the
  `Ownable` zero-address check is overridden away);
* `acceptOwnership()` (`Ownable2Step.sol:52-56`): the caller must be the pending owner; it becomes
  the owner and the pending owner is deleted (`_transferOwnership`, `Ownable2Step.sol:44-47`);
* `renounceOwnership()` (`Ownable.sol:61-63`): `onlyOwner`, owner and pending owner become zero.

The views `isPairAllowed` (`:73-78`), `isAllowedDAConfiguration`, `owner` and `pendingOwner` change
nothing and are not steps. The contract has no constructor of its own; `Ownable`'s constructor
(`Ownable.sol:28-30`) makes the deployer the owner (`deploy`).

## Model boundaries

* An address is a word. `L2DACommitmentScheme` is the five-constructor enum of
  `common/Config.sol:49-55`; an out-of-range enum argument reverts at ABI decoding, so it is not
  representable.
* A revert is the absence of a step. `exec` returns `none` exactly on the source's reverts.
* `updateDAPairUnchecked` and `updateDAPairNoOwner` are not source functions. They are the source
  function with one guard deleted, used only by the countermodels.
-/

namespace Contracts.DataAvailability

/-- `L2DACommitmentScheme` (`common/Config.sol:49-55`). -/
inductive L2DACommitmentScheme
  | NONE
  | EMPTY_NO_DA
  | PUBDATA_KECCAK256
  | BLOBS_AND_PUBDATA_KECCAK256
  | BLOBS_ZKSYNC_OS
deriving DecidableEq, Repr

/-- The storage of a `RollupDAManager`. -/
structure Manager where
  /-- `Ownable._owner`. -/
  owner : Address
  /-- `Ownable2Step._pendingOwner`. -/
  pendingOwner : Address
  /-- `isAllowedDAConfiguration` (`RollupDAManager.sol:22-23`). -/
  allowed : Address → L2DACommitmentScheme → Bool

/-- The state right after deployment by `deployer`: `Ownable`'s constructor sets the owner
(`Ownable.sol:28-30`); everything else is zero. -/
def deploy (deployer : Address) : Manager :=
  { owner := deployer, pendingOwner := 0, allowed := fun _ _ => false }

/-- One external call, with its `msg.sender`. -/
inductive MCall
  | updateDAPair (caller v : Address) (s : L2DACommitmentScheme) (status : Bool)
  | transferOwnership (caller newOwner : Address)
  | acceptOwnership (caller : Address)
  | renounceOwnership (caller : Address)
deriving DecidableEq

/-- `msg.sender` of a call. -/
def MCall.caller : MCall → Address
  | .updateDAPair c _ _ _ => c
  | .transferOwnership c _ => c
  | .acceptOwnership c => c
  | .renounceOwnership c => c

/-- `isAllowedDAConfiguration[v][s] = status` (`RollupDAManager.sol:63`). -/
def setPair (M : Manager) (v : Address) (s : L2DACommitmentScheme) (status : Bool) : Manager :=
  { M with allowed := fun v' s' => if v' = v ∧ s' = s then status else M.allowed v' s' }

/-- **ONE CALL** of the contract, guards in source order; `none` is a revert. -/
def exec (M : Manager) : MCall → Option Manager
  -- `RollupDAManager.sol:58-66`: `onlyOwner` (`Ownable.sol:35-38, 50-52`), then
  -- `validDAConfiguration` (`:34-43`), then the write (`:63`).
  | .updateDAPair c v s st =>
      if c ≠ M.owner then none
      else if v = 0 then none
      else if s = .NONE then none
      else some (setPair M v s st)
  -- `Ownable2Step.sol:35-38`
  | .transferOwnership c n =>
      if c ≠ M.owner then none
      else some { M with pendingOwner := n }
  -- `Ownable2Step.sol:52-56`, then `_transferOwnership` (`:44-47`, `Ownable.sol:78-81`)
  | .acceptOwnership c =>
      if M.pendingOwner ≠ c then none
      else some { M with owner := c, pendingOwner := 0 }
  -- `Ownable.sol:61-63`, then `_transferOwnership(address(0))`
  | .renounceOwnership c =>
      if c ≠ M.owner then none
      else some { M with owner := 0, pendingOwner := 0 }

/-! ## Runs -/

/-- A run of successful calls, each logged with the state it was called in, oldest first.
Any interleaving of the four entry points, by any callers. -/
inductive ReachLog : Manager → Manager → List (Manager × MCall) → Prop
  | refl {M : Manager} : ReachLog M M []
  | tail {M₀ M M' : Manager} {log : List (Manager × MCall)} {c : MCall} :
      ReachLog M₀ M log → exec M c = some M' → ReachLog M₀ M' (log ++ [(M, c)])

/-- Reachability: some logged run connects the two states. -/
def Reach (M₀ M : Manager) : Prop := ∃ log, ReachLog M₀ M log

/-- The status the last logged `updateDAPair` on `(v, s)` wrote, if any. -/
def lastStatus (log : List (Manager × MCall)) (v : Address) (s : L2DACommitmentScheme) :
    Option Bool :=
  log.foldl (fun acc e => match e.2 with
    | .updateDAPair _ v' s' st => if v' = v ∧ s' = s then some st else acc
    | _ => acc) none

/-- The pairs `isPairAllowed` must never report: the zero validator, or the `NONE` scheme. -/
def NoInvalidPairs (M : Manager) : Prop :=
  (∀ s, M.allowed 0 s = false) ∧ ∀ v, M.allowed v .NONE = false

/-- `a` was nominated as the next owner: it was the pending owner at the start of the run, or some
logged `transferOwnership` by the then-owner named it. -/
def Nominated (M₀ : Manager) (log : List (Manager × MCall)) (a : Address) : Prop :=
  a = M₀.pendingOwner ∨ ∃ pre, (pre, MCall.transferOwnership pre.owner a) ∈ log

/-! ## Guard-deleted variants (countermodels only) -/

/-- `updateDAPair` with the `validDAConfiguration` modifier deleted. Not a source function. -/
def updateDAPairUnchecked (M : Manager) (c v : Address) (s : L2DACommitmentScheme) (st : Bool) :
    Option Manager :=
  if c ≠ M.owner then none else some (setPair M v s st)

/-- `updateDAPair` with `onlyOwner` deleted. Not a source function. -/
def updateDAPairNoOwner (M : Manager) (v : Address) (s : L2DACommitmentScheme) (st : Bool) :
    Option Manager :=
  if v = 0 then none else if s = .NONE then none else some (setPair M v s st)

end Contracts.DataAvailability
